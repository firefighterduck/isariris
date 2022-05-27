theory CoreStructures
imports COFEs
begin

section \<open> Core Structures \<close>
text \<open> This section introduces the concepts of cameras, resource algebras and related structures. \<close>
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
      \<exists>c1 c2. (a = c1 \<cdot> c2 \<and> n_equiv n c1 b1 \<and> n_equiv n c2 b2)"
begin
abbreviation n_valid :: "'a \<Rightarrow> nat \<Rightarrow> bool" where "n_valid x \<equiv> Rep_sprop (valid_raw x)"

definition valid :: "'a \<Rightarrow> bool" where
  "valid a = (\<forall>n. n_valid a n)"

definition incl :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "incl a b = (\<exists>c. b = a \<cdot> c)"

definition n_incl :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "n_incl n a b = (\<exists>c. n_equiv n b (a \<cdot> c))"

(* Frame-preserving update *)
definition camera_upd :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<leadsto>" 50) where
  "a\<leadsto>B \<equiv> (\<forall>n x. n_valid (a \<cdot> x) n \<longrightarrow> (\<exists>b\<in>B. n_valid (b \<cdot> x) n))"

definition camera_updP :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" (infix "\<leadsto>:" 50) where
  "a \<leadsto>: P \<equiv> \<forall>n x. n_valid (a \<cdot> x) n \<longrightarrow> (\<exists>b. P b \<and> n_valid (b \<cdot> x) n)"

(* Auxiliary camera lemmas *)
lemmas valid_raw_ne [elim] = non_expansiveE[OF valid_raw_non_expansive]  
lemmas pcore_ne [elim] = non_expansiveE[OF pcore_non_expansive]
lemmas op_ne [elim] = non_expansive2E[OF op_non_expansive]

lemma camera_upd_refl: "a\<leadsto>{a}" unfolding camera_upd_def by simp

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
  "\<lbrakk>n_equiv n a (b \<cdot> c); n_equiv m b d; n\<le>m\<rbrakk> \<Longrightarrow> n_equiv n a (d \<cdot> c)"
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

lemma pcore_mono: "\<lbrakk>\<forall>x. \<exists>y. pcore x = Some y; incl a b\<rbrakk> \<Longrightarrow> incl (the (pcore a)) (the (pcore b))"
  apply (auto simp: incl_def) using local.camera_pcore_mono by fastforce

lemmas camera_props = camera_assoc camera_comm camera_pcore_id camera_pcore_idem camera_pcore_mono
  camera_valid_op camera_extend valid_raw_ne pcore_ne op_ne
end

lemma n_incl_incl: "n_incl n (a::'a::{camera,discrete}) b \<longleftrightarrow> incl a b"
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

lemma camera_core_n_valid: "n_valid a n \<Longrightarrow> n_valid (core a) n"
  by (metis camera_core_id local.camera_valid_op) 
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

lemma total_n_incl_extend: "\<lbrakk>n_equiv n a b; m\<le>n\<rbrakk> \<Longrightarrow> n_incl m (a\<cdot>c) (b\<cdot>c)"
  using total_n_inclI n_incl_extend by blast

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

text \<open>The semantics of the \<^class>\<open>core_id\<close> class but for single values.\<close>
definition pcore_id_pred :: "'a::total_camera \<Rightarrow> bool" where
  "pcore_id_pred a \<equiv> pcore a = Some a"  

lemma core_id_pred: "pcore_id_pred a \<longleftrightarrow> core a = a"
  by (auto simp: pcore_id_pred_def core_def) (metis option.sel total_pcore)

lemma \<epsilon>_pcore_id_def: "pcore_id_pred \<epsilon>"
  by (auto simp: pcore_id_pred_def \<epsilon>_pcore)

lemma core_id_pcore_idpred [simp]: "pcore_id_pred (a::'a::{core_id,total_camera})"
  by (simp add: pcore_id_pred_def pcore_id)
  
text \<open>Discrete Camera - A camera based on a discrete OFE with non-step indexed validity.\<close>
class dcamera = camera + discrete + assumes d_valid: "n_valid x 0 \<Longrightarrow> valid x"
begin
lemma dcamera_valid_iff: "valid x \<longleftrightarrow> n_valid x n"
by (auto simp: d_valid)(auto simp: valid_def)
end

definition dcamera_val :: "'a::camera \<Rightarrow> bool" where
  "dcamera_val v \<equiv> discrete_val v \<and> (n_valid v 0 \<longrightarrow> valid v)"

lemma dcamera_dcamera_val [simp]: "dcamera_val (x::'a::dcamera)"
  by (simp add: dcamera_val_def d_valid discrete_val_def d_equiv d_eq)

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

(* Index into resource maps to allow more than one instance of a camera *)
type_synonym gname = nat

text \<open>Locale to denote that a resource type contains a certain camera type. Allows modular proofs.\<close>
locale inG = 
fixes get_cmra :: "gname \<Rightarrow> 'a::ucamera \<Rightarrow> 'b::camera option"
  and put_cmra :: "gname \<Rightarrow> 'b \<Rightarrow> 'a"
assumes get_put: "get_cmra \<gamma> (put_cmra \<gamma> x) = Some x"
  and put_ne: "n_equiv n (put_cmra \<gamma> x) (put_cmra \<gamma> y) \<longleftrightarrow> n_equiv n x y"
  and put_ne2: "n_equiv n (put_cmra \<gamma> x) z \<Longrightarrow> \<exists>y'. z=put_cmra \<gamma> y'"
  and put_n_valid: "n_valid (put_cmra \<gamma> x) n \<longleftrightarrow> n_valid x n"
  and put_pcore: "pcore (put_cmra \<gamma> x) = Some (case (pcore x) of Some y \<Rightarrow> (put_cmra \<gamma> y) | None \<Rightarrow> \<epsilon>)"
  and put_op: "put_cmra \<gamma> (x \<cdot> y) = (put_cmra \<gamma> x) \<cdot> (put_cmra \<gamma> y)"
begin
  lemma put_valid: "valid (put_cmra \<gamma> x) \<longleftrightarrow> valid x"
    by (auto simp: valid_def put_n_valid)
end
end