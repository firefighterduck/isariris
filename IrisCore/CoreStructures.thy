theory CoreStructures
imports OFEs
begin

section \<open> Core Structures \<close>
text \<open> This section introduces the concepts of cameras, resource algebras and related structures. \<close>
subsection \<open>Non-expansive functions\<close>
text \<open>Non-expansive functions, i.e. equivalence persisting functions from one OFE to another.\<close>
definition non_expansive :: "('a::ofe \<Rightarrow>'b::ofe) \<Rightarrow> bool" where 
  "non_expansive ne \<equiv> \<forall>x y n. n_equiv n x y \<longrightarrow> n_equiv n (ne x) (ne y)"

lemma non_expansiveI[intro?]: "\<lbrakk>\<And>n x y. n_equiv n x y \<Longrightarrow> n_equiv n (f x) (f y)\<rbrakk> \<Longrightarrow> non_expansive f"
  unfolding non_expansive_def by simp
lemma non_expansiveE[elim]: "non_expansive f \<Longrightarrow> 
  (\<And>n x y. \<lbrakk>n_equiv n x y; f x=x'; f y=y'\<rbrakk> \<Longrightarrow> n_equiv n x' y')"
  using non_expansive_def by blast

definition non_expansive2 :: "('a::ofe \<Rightarrow> 'b::ofe \<Rightarrow> 'c::ofe) \<Rightarrow> bool" where
  "non_expansive2 ne \<equiv> \<forall>x y a b n. n_equiv n x y \<longrightarrow> n_equiv n a b \<longrightarrow> n_equiv n (ne x a) (ne y b)"

lemma non_expansive2I[intro?]: "(\<And>x y a b n. n_equiv n x y \<Longrightarrow> n_equiv n a b \<Longrightarrow> 
  n_equiv n (f x a) (f y b)) \<Longrightarrow> non_expansive2 f"
  using non_expansive2_def by blast
lemma non_expansive2E[elim]: "non_expansive2 f \<Longrightarrow> 
  (\<And>n x y a b. \<lbrakk>n_equiv n x y; n_equiv n a b; f x a=x'; f y b=y'\<rbrakk> \<Longrightarrow> n_equiv n x' y')"
  using non_expansive2_def by blast

lemma non_expansive2_ne:"non_expansive2 f \<Longrightarrow> non_expansive (f x)"
  by (auto simp: non_expansive_def non_expansive2_def ofe_eq_limit)

lemma sprop_ne: "non_expansive (Rep_sprop P)"
  unfolding non_expansive_def n_equiv_nat_def n_equiv_bool_def by simp
  
lemma ne_sprop_weaken: 
  "\<lbrakk>n_equiv n x y; m\<le>n; non_expansive P; Rep_sprop (P x) n\<rbrakk> \<Longrightarrow> Rep_sprop (P y) m"
  using Rep_sprop n_equiv_sprop_def non_expansive_def by blast

lemma ne_sprop_weaken2:
  "\<lbrakk>n_equiv n x y; n_equiv n a b; m\<le>n; non_expansive2 P; Rep_sprop (P x a) n\<rbrakk> \<Longrightarrow> Rep_sprop (P y b) m"
  using Rep_sprop n_equiv_sprop_def non_expansive2_def by fast

lemma ne_comp: "\<lbrakk>non_expansive f; non_expansive g\<rbrakk> \<Longrightarrow> non_expansive (f \<circ> g)"
  by (auto simp: non_expansive_def)

lemma discrete_ne: "non_expansive (f::'a::discrete\<Rightarrow>'b::discrete)"
  by (rule non_expansiveI) (simp add: d_equiv)
  
text \<open>The corresponding subtype of non-expansive functions.\<close>
typedef (overloaded) ('a, 'b) ne = "{f::'a::ofe\<Rightarrow>'b::ofe. non_expansive f}"
  using sprop_ne[of sTrue] apply simp
  by (metis non_expansiveI ofe_refl)
type_notation ne (infix "-n>" 60)
setup_lifting type_definition_ne
lemmas [simp] = Rep_ne_inverse Rep_ne_inject
lemmas [simp, intro!] = Rep_ne[unfolded mem_Collect_eq]

instantiation ne :: (ofe,ofe) ofe begin
lift_definition n_equiv_ne :: "nat \<Rightarrow> 'a-n>'b \<Rightarrow> 'a-n>'b \<Rightarrow> bool" is
  "\<lambda>n f g. \<forall>x. n_equiv n (f x) (g x)" .
lift_definition ofe_eq_ne :: "'a-n>'b \<Rightarrow> 'a-n>'b \<Rightarrow> bool" is
  "\<lambda>f g. \<forall>x. ofe_eq  (f x) (g x)" .
instance by (standard; transfer) (auto simp: ofe_refl ofe_sym ofe_limit intro: ofe_trans ofe_mono)
end

lift_definition ne_chain :: "('a::ofe,'b::ofe) ne chain \<Rightarrow> 'a \<Rightarrow> 'b chain" is
  "\<lambda>c x n. Rep_ne (c n) x" apply transfer unfolding non_expansive_def by auto
  
instantiation ne :: (ofe,cofe) cofe begin
lift_definition lim_ne :: "('a, 'b) ne chain \<Rightarrow> ('a, 'b) ne" is
  "\<lambda>c x. lim (ne_chain c x)"
  by (metis (no_types, lifting) Rep_ne core_compl mem_Collect_eq ne_chain.rep_eq non_expansive_def 
    ofe_sym ofe_trans)
instance apply standard apply (simp add: n_equiv_ne_def lim_ne.rep_eq ne_chain_def)
  by (smt (verit, best) Abs_chain_inverse Rep_chain core_compl mem_Collect_eq ne_chain.rep_eq)
end

lift_definition ne_id :: "'a::ofe -n> 'a" is "id" by (rule non_expansiveI) simp
lift_definition ne_const :: "'b::ofe \<Rightarrow> 'a::ofe -n> 'b" is "\<lambda>b _. b" 
  by (rule non_expansiveI) (rule ofe_refl)

lift_definition ne_comp :: "'b::ofe -n> 'c::ofe \<Rightarrow> 'a::ofe -n> 'b \<Rightarrow> 'a-n>'c" is
  "\<lambda>f g. f \<circ> g" by (rule ne_comp)

definition ne_map :: "('a2::ofe-n>'a1::ofe) \<Rightarrow> ('b1::ofe-n>'b2::ofe) \<Rightarrow> ('a1-n>'b1) \<Rightarrow> ('a2-n>'b2)" where
  "ne_map f g h = ne_comp g (ne_comp h f)"

lift_definition ne_map_ne :: "('a2::ofe-n>'a1::ofe) \<Rightarrow> ('b1::ofe-n>'b2::ofe) \<Rightarrow> (('a1-n>'b1)-n>('a2-n>'b2))" is
  "\<lambda>f g. ne_map f g" unfolding ne_map_def ne_comp_def apply simp using ne_comp Rep_ne_inverse
  by (smt (verit) Rep_ne mem_Collect_eq n_equiv_ne.rep_eq ne_comp.rep_eq non_expansive_def o_def)
  
subsection \<open>Contractive functions\<close>
definition contractive :: "('a::ofe \<Rightarrow> 'b::ofe) \<Rightarrow> bool" where
  "contractive con \<equiv> \<forall>n x y. (\<forall>m<n. n_equiv m x y) \<longrightarrow> n_equiv n (con x) (con y)"  

definition contractive_alt :: "('a::ofe \<Rightarrow> 'b::ofe) \<Rightarrow> bool" where
  "contractive_alt f \<equiv> \<forall>n x y. (case n of 0 \<Rightarrow> True | Suc n' \<Rightarrow> n_equiv n' x y) \<longrightarrow> n_equiv n (f x) (f y)"

lemma contr_contr_alt: "contractive f \<longleftrightarrow> contractive_alt f"
  apply (simp add: contractive_def contractive_alt_def split: nat.splits)
  by (smt (verit, ccfv_SIG) bot_nat_0.extremum_strict ex_least_nat_less less_Suc_eq_le nat_less_le ofe_down_contr order.refl)

lemma contractiveI: "(\<And>n x y. (\<forall>m<n. n_equiv m x y) \<Longrightarrow> n_equiv n (f x) (f y)) \<Longrightarrow> contractive f"
  by (auto simp: contractive_def)

lemma contractiveE: "contractive f \<Longrightarrow> (\<And>n x y. (\<forall>m<n. n_equiv m x y) \<Longrightarrow> n_equiv n (f x) (f y))"
  by (auto simp: contractive_def)
  
lemma contractive_non_expansive: "contractive f \<Longrightarrow> non_expansive f"
  by (auto simp: less_imp_le_nat intro: non_expansiveI ofe_mono[OF less_imp_le_nat] elim!: contractiveE)

lemma next_contr: "contractive Next"
  apply (rule contractiveI) 
  apply (simp add: n_equiv_later_def)
  using diff_Suc_less by blast
  
text \<open>The corresponding subtype of contractive functions.\<close>
typedef (overloaded) ('a::ofe,'b::ofe) contr = "{f::'a\<Rightarrow>'b. contractive f}"
  using contractiveI ofe_eq_limit by fastforce
setup_lifting type_definition_contr
lemmas [simp] = Rep_contr_inverse Rep_contr_inject
lemmas [simp, intro!] = Rep_contr[unfolded mem_Collect_eq]

subsection \<open>Resource Algebra\<close>
class ra =
  fixes valid :: "'a \<Rightarrow> bool"
    and core :: "'a \<Rightarrow> 'a option"
    and op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ra_assoc: "op (op a b) c = op a (op b c)"
    and ra_comm: "op a b = op b a"
    and ra_core_id: "\<exists>a'. core a = Some a' \<Longrightarrow> op (the (core a)) a = a"
    and ra_core_idem: "\<exists>a'. core a = Some a' \<Longrightarrow> core (the (core a)) = core a"
    and ra_core_mono: "\<lbrakk>\<exists>a'. core a = Some a'; \<exists>c. b=op a c\<rbrakk> \<Longrightarrow> 
      (\<exists>b'. (core b = Some b') \<and> (\<exists>c. (the (core b)) = op (the (core a)) c))"
    and ra_valid_op: "valid (op a b) \<Longrightarrow> valid a"

subsection \<open>Camera\<close>
text \<open>Camera, a more general notion of resource algebras based on an OFE.\<close>
class camera = ofe +
  fixes valid_raw :: "'a::ofe \<Rightarrow> sprop" and pcore :: "'a \<Rightarrow> 'a option" 
    and op :: "'a \<Rightarrow>'a \<Rightarrow> 'a" (infixl "\<cdot>" 60)
  assumes valid_raw_non_expansive: "non_expansive valid_raw" 
    and pcore_non_expansive: "non_expansive pcore" 
    and op_non_expansive: "non_expansive2 op" 
    and camera_assoc: "(a \<cdot> b) \<cdot> c = a \<cdot> (b \<cdot> c)"
    and camera_comm: "a \<cdot> b = b \<cdot> a"
    and camera_pcore_id: "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a"
    and camera_pcore_idem: "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
    and camera_pcore_mono: "\<lbrakk>pcore a = Some a'; \<exists>c. b= a \<cdot> c\<rbrakk> \<Longrightarrow>
      (\<exists>b'. (pcore b = Some b') \<and> (\<exists>c. b' = a' \<cdot> c))"
    and camera_valid_op: "Rep_sprop (valid_raw (a \<cdot> b)) n 
      \<Longrightarrow> Rep_sprop (valid_raw a) n"
    and camera_extend: "\<lbrakk>Rep_sprop (valid_raw a) n; n_equiv n a (b1 \<cdot> b2)\<rbrakk> \<Longrightarrow>
      \<exists>c1 c2. (a = c1 \<cdot>  c2 \<and> n_equiv n c1 b1 \<and> n_equiv n c2 b2)"
begin
abbreviation n_valid :: "'a \<Rightarrow> nat \<Rightarrow> bool" where "n_valid x \<equiv> Rep_sprop (valid_raw x)"

definition valid :: "'a \<Rightarrow> bool" where
  "valid a = (\<forall>n. n_valid a n)"

definition incl :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "incl a b = (\<exists>c. b = a \<cdot> c)"

definition n_incl :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "n_incl n a b = (\<exists>c. n_equiv n b (a \<cdot> c))"

(* Frame-preserving update *)
definition fup :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<leadsto>" 50) where
  "a\<leadsto>B \<equiv> (\<forall>x::'a. valid a \<longrightarrow> valid (a \<cdot> x) \<longrightarrow> (\<exists>b\<in>B. valid (b \<cdot> x)))"

(* Auxiliary camera lemmas *)
lemmas valid_raw_ne [elim] = non_expansiveE[OF valid_raw_non_expansive]  
lemmas pcore_ne [elim] = non_expansiveE[OF pcore_non_expansive]
lemmas op_ne [elim] = non_expansive2E[OF op_non_expansive]

lemma camera_n_incl_le: "\<lbrakk>n_incl n x y; m\<le>n\<rbrakk> \<Longrightarrow> n_incl m x y"
  by (auto simp: n_incl_def) (meson ofe_class.ofe_mono)

lemma op_equiv: "\<lbrakk>n_equiv n x y; n_equiv n a b\<rbrakk> \<Longrightarrow> n_equiv n (x \<cdot> a) (y \<cdot> b)"
proof -
  assume "n_equiv n x y" "n_equiv n a b"
  hence "n_equiv n (x,a) (y,b)" by simp
  thus "n_equiv n (op x a) (op y b)" 
    using op_non_expansive non_expansive2_def by fastforce
qed  

lemma op_equiv_subst: 
  "\<lbrakk>n_equiv n a (op b c); n_equiv m b d; n\<le>m\<rbrakk> \<Longrightarrow> n_equiv n a (d \<cdot> c)"
  by (meson op_equiv ofe_class.ofe_mono ofe_class.ofe_refl ofe_class.ofe_trans)

lemma valid_op_op_weaken: "\<lbrakk>n_equiv n x (y \<cdot> z); n_valid (x \<cdot> x') n\<rbrakk> 
  \<Longrightarrow> n_valid (op (op y z) x') n"
proof -
  assume assm1: "n_equiv n x (y \<cdot> z)" 
  assume assm2: "n_valid (x \<cdot> x') n"
  from assm1 have "n_equiv n (x \<cdot> x') ((y \<cdot> z) \<cdot> x')" 
    by (simp add: ofe_class.ofe_refl op_equiv)
  from ne_sprop_weaken[OF this order.refl valid_raw_non_expansive assm2]
  show "n_valid ((y \<cdot> z) \<cdot> x') n" .
qed

lemma n_valid_incl_subst: "\<lbrakk>n_incl n a b; n_valid (b \<cdot> c) m; m\<le>n\<rbrakk> 
  \<Longrightarrow> n_valid (a \<cdot> c) m"
  using n_incl_def
  by (smt (verit, ccfv_threshold) camera_assoc camera_comm camera_valid_op ofe_class.ofe_mono valid_op_op_weaken)

lemma n_valid_ne: "\<lbrakk>n_equiv n x y; n_valid x n\<rbrakk> \<Longrightarrow> n_valid y n"
proof -
  assume assms: "n_equiv n x y" "n_valid x n"
  then show "Rep_sprop (valid_raw y) n" using valid_raw_non_expansive ne_sprop_weaken by blast
qed

lemma incl_op_extend: "incl a b \<Longrightarrow> incl a (b \<cdot> c)"
  by (auto simp: incl_def camera_assoc)
lemma n_incl_op_extend: "n_incl n a (a \<cdot> c)"
  by (meson n_incl_def ofe_class.ofe_eq_limit)
lemma n_incl_extend: "\<lbrakk>n_incl n a b; m\<le>n\<rbrakk> \<Longrightarrow> n_incl m (a \<cdot> c) (b \<cdot> c)"
  using n_incl_def
  by (smt (verit, ccfv_SIG) camera_n_incl_le local.camera_assoc local.camera_comm ofe_class.ofe_eq_limit op_ne)
lemma incl_n_incl: "incl a b \<Longrightarrow> n_incl n a b"
  using ofe_class.ofe_refl by (auto simp: incl_def n_incl_def) 

lemmas camera_props = camera_assoc camera_comm camera_pcore_id camera_pcore_idem camera_pcore_mono
  camera_valid_op camera_extend valid_raw_ne pcore_ne op_ne
end

lemma n_incl_incl: "(\<forall>n. n_incl n (a::'a::{camera,discrete}) b) \<longleftrightarrow> incl a b"
 by (auto simp: incl_def n_incl_def d_equiv)

subsection \<open>Camera Extensions\<close>
text \<open>Total Camera - A camera with a total core\<close> 
class total_camera = camera +
  assumes total_pcore: "\<exists>b. pcore a = Some b"
begin
definition core :: "'a \<Rightarrow> 'a" where
  "core = the \<circ> pcore"

lemma core_ne: "non_expansive core"
  unfolding non_expansive_def core_def 
  by (smt (verit, del_insts) comp_apply local.pcore_ne n_equiv_option_def ofe_class.ofe_refl option.sel)

lemma camera_core_id: "(core a) \<cdot> a = a"
  and camera_core_idem: "core (core a) = core a"
  and camera_core_mono: "incl a b \<Longrightarrow> incl (core a) (core b)"
  apply (simp_all add: core_def incl_def comp_def camera_pcore_id total_pcore camera_pcore_idem)
  using camera_pcore_mono total_pcore by fastforce

lemma camera_core_mono_n: "n_incl n a b \<Longrightarrow> n_incl n (core a) (core b)"
  by (metis core_ne local.incl_def local.n_incl_def non_expansiveE camera_core_mono)
end 

text \<open>Unital Camera - A camera with a unit element\<close>
class ucamera = camera +
  fixes \<epsilon>
  assumes \<epsilon>_valid: "valid \<epsilon>"
    and \<epsilon>_left_id: "\<epsilon> \<cdot> a = a"
    and \<epsilon>_pcore: "pcore \<epsilon> = Some \<epsilon>"
begin
subclass total_camera
proof
  fix a
  from \<epsilon>_left_id have "\<exists>c. a = \<epsilon> \<cdot> c" by metis
  from camera_pcore_mono[OF \<epsilon>_pcore this] show "\<exists>b. pcore a = Some b" by auto
qed

lemma \<epsilon>_core: "core \<epsilon> = \<epsilon>" using core_def \<epsilon>_pcore by simp

lemma total_n_inclI: "n2\<le>n1 \<Longrightarrow> n_equiv n1 x1 x2 \<Longrightarrow> n_incl n2 x1 (x2::'a)"
proof (unfold n_incl_def; standard)
  assume "n2\<le>n1" "n_equiv n1 x1 x2"
  then have "n_equiv n2 x1 x2" by (rule ofe_class.ofe_mono)
  then have "n_equiv n2 (op x1 \<epsilon>) x2" 
    by (metis camera_comm \<epsilon>_left_id)
  then show "n_equiv n2 x2 (op x1 \<epsilon>)" by (simp add: ofe_class.ofe_sym)
qed

lemma n_incl_\<epsilon>[simp]: "n_incl n \<epsilon> a"
proof (unfold n_incl_def)
  have "n_equiv n a a" by (simp add: ofe_class.ofe_refl)
  then have "n_equiv n a (\<epsilon>\<cdot>a)" by (simp add: \<epsilon>_left_id)
  then show "\<exists>c. n_equiv n a (\<epsilon> \<cdot> c)" by fast
qed

lemma \<epsilon>_right_id: "a\<cdot>\<epsilon>=a"
  by (auto simp: \<epsilon>_left_id camera_comm)

lemma n_incl_refl[simp]: "n_incl n a a"
proof (unfold n_incl_def)
  have "n_equiv n a (a\<cdot>\<epsilon>)"
    by (auto simp: \<epsilon>_right_id ofe_class.ofe_refl)
  then show "\<exists>c. n_equiv n a (a \<cdot> c)" by auto
qed

lemma \<epsilon>_n_valid: "n_valid \<epsilon> n" by (simp add: \<epsilon>_valid[unfolded valid_def])
end

text \<open>A camera with the identity for its core.\<close>
class core_id = camera + assumes pcore_id: "pcore a = Some a"
begin
lemma the_core_id: "the (pcore a) = a" by (simp add: pcore_id)
end

lemma core_id: "core (a::'a::{core_id,total_camera}) = a"
  by (simp add: the_core_id core_def)

text \<open>The semantics of the core_id class but for single values.\<close>
definition pcore_id_pred :: "'a::total_camera \<Rightarrow> bool" where
  "pcore_id_pred a \<equiv> pcore a = Some a"  

lemma core_id_pred: "pcore_id_pred a \<longleftrightarrow> core a = a"
  by (auto simp: pcore_id_pred_def core_def) (metis option.sel total_pcore)

lemma \<epsilon>_pcore_id_def: "pcore_id_pred \<epsilon>"
  by (auto simp: pcore_id_pred_def \<epsilon>_pcore)

text \<open>Discrete Camera - A camera based on a discrete OFE with non-step indexed validity.\<close>
class dcamera = camera + discrete + assumes d_valid: "n_valid x 0 \<Longrightarrow> valid x"
begin
lemma dcamera_valid_iff: "valid x \<longleftrightarrow> n_valid x n"
by (auto simp: d_valid)(auto simp: valid_def)
end

text \<open>Discrete Unital Camera\<close>
class ducamera = dcamera + ucamera

subsection \<open>Camera morphisms\<close>
text \<open>Camera morphisms as a locale, ...\<close>
locale camera_morphism = fixes f :: "'a::ucamera \<Rightarrow> 'b::ucamera"
  assumes morphism_ne: "non_expansive f"
  and morphism_valid: "n_valid x n \<Longrightarrow> n_valid (f x) n"
  and morphism_pcore: "map_option f (pcore x) = pcore (f x)"
  and morphism_op: "f (x \<cdot> y) = (f x) \<cdot> (f y)"

interpretation id_morph: camera_morphism id 
  by unfold_locales (auto simp: non_expansive_def option.map_id)

interpretation const_\<epsilon>_morph: camera_morphism "\<lambda>_. \<epsilon>"
  by unfold_locales (auto simp: non_expansive_def ofe_refl \<epsilon>_n_valid \<epsilon>_pcore \<epsilon>_left_id total_pcore)

lemma n_incl_morph: "\<lbrakk>camera_morphism f; n_incl n x y\<rbrakk> \<Longrightarrow> n_incl n (f x) (f y)"
  by (auto simp: n_incl_def camera_morphism_def) fast

lemma comp_morph: "\<lbrakk>camera_morphism f; camera_morphism g\<rbrakk> \<Longrightarrow> camera_morphism (f \<circ> g)"
   by (transfer; auto simp: camera_morphism_def ne_comp) (metis option.map_comp)

text \<open>... and as a semantic subtype.\<close>
typedef (overloaded) ('a::ucamera,'b::ucamera) cmra_morph = "{f::'a \<Rightarrow> 'b. camera_morphism f}"
  using const_\<epsilon>_morph.camera_morphism_axioms by auto
setup_lifting type_definition_cmra_morph
lemmas [simp] = Rep_cmra_morph_inverse Rep_cmra_morph_inject
lemmas [simp, intro!] = Rep_cmra_morph[unfolded mem_Collect_eq]

lift_definition id_morph :: "('a::ucamera, 'a) cmra_morph" is "id::('a\<Rightarrow>'a)" 
  by (rule id_morph.camera_morphism_axioms)

lift_definition morph_comp :: "('b::ucamera,'c::ucamera) cmra_morph \<Rightarrow> ('a::ucamera,'b) cmra_morph \<Rightarrow> ('a,'c) cmra_morph" is
  "\<lambda>(f::('b,'c) cmra_morph) (g::('a,'b) cmra_morph). (Rep_cmra_morph f) \<circ> (Rep_cmra_morph g)"
  using comp_morph by blast

instantiation cmra_morph :: (ucamera,ucamera) ofe begin
lift_definition n_equiv_cmra_morph :: "nat \<Rightarrow> ('a, 'b) cmra_morph \<Rightarrow> ('a, 'b) cmra_morph \<Rightarrow> bool" is
  "\<lambda>n f g. \<forall>x. n_equiv n (f x) (g x)" .
lift_definition ofe_eq_cmra_morph :: "('a, 'b) cmra_morph \<Rightarrow> ('a, 'b) cmra_morph \<Rightarrow> bool" is
  "\<lambda>f g. \<forall>x. ofe_eq (f x) (g x)" .
instance by (standard; transfer) (auto simp: ofe_refl ofe_sym ofe_limit intro: ofe_trans ofe_mono)
end

instance cmra_morph :: (ducamera,ducamera) discrete by (standard; transfer) (auto simp: d_equiv d_eq)
end