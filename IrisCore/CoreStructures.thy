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

definition opM :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" (infixl "\<cdot>?" 60) where
  "x \<cdot>? my \<equiv> case my of Some y \<Rightarrow> x \<cdot> y | None \<Rightarrow> x"

(* Frame-preserving update *)
definition camera_upd :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<leadsto>" 50) where
  "a\<leadsto>b \<equiv> (\<forall>n x. n_valid (a \<cdot>? x) n \<longrightarrow> n_valid (b \<cdot>? x) n)"

definition camera_updP :: "'a \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" (infix "\<leadsto>:" 50) where
  "a \<leadsto>: P \<equiv> \<forall>n x. n_valid (a \<cdot>? x) n \<longrightarrow> (\<exists>b. P b \<and> n_valid (b \<cdot>? x) n)"

(* Auxiliary camera lemmas *)
lemmas valid_raw_ne [elim] = non_expansiveE[OF valid_raw_non_expansive]  
lemmas pcore_ne [elim] = non_expansiveE[OF pcore_non_expansive]
lemmas op_ne [elim] = non_expansive2E[OF op_non_expansive]

lemma camera_upd_refl: "a\<leadsto>a" unfolding camera_upd_def by simp

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

lemma incl_n_valid: "\<lbrakk>incl a b; n_valid b n\<rbrakk> \<Longrightarrow> n_valid a n"
  by (auto simp: incl_def intro: camera_valid_op)

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

lemma n_incl_reduce: "n_incl n (a \<cdot> b) c \<Longrightarrow> n_incl n a c"
  using local.camera_assoc n_incl_def by auto

lemma n_incl_reduce2: "n_incl n (a \<cdot> b) c \<Longrightarrow> n_incl n b c"
  using camera_assoc n_incl_def camera_comm by metis

lemmas camera_props = camera_assoc camera_comm camera_pcore_id camera_pcore_idem camera_pcore_mono
  camera_valid_op camera_extend valid_raw_ne pcore_ne op_ne
end

lemma n_incl_incl: "n_incl n (a::'a::{camera,discrete}) b \<longleftrightarrow> incl a b"
 by (auto simp: incl_def n_incl_def d_equiv)
 
definition camera_mono_n :: "('a::camera \<Rightarrow> 'b::camera) \<Rightarrow> bool" where
  "camera_mono_n f = (\<forall>x y n. n_equiv n (f x \<cdot> f y) (f (x \<cdot> y)))"

definition camera_mono :: "('a::camera \<Rightarrow> 'b::camera) \<Rightarrow> bool" where
  "camera_mono f = (\<forall>x y. f x \<cdot> f y = f (x \<cdot> y))"

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

lemma total_update: "x\<leadsto>y \<longleftrightarrow> (\<forall>n z. n_valid (x \<cdot> z) n \<longrightarrow> n_valid (y \<cdot> z) n)"
  apply (auto simp: camera_upd_def opM_def split: option.splits)
  by (metis camera_core_id camera_comm camera_valid_op)
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

definition lup :: "'a\<times>'a \<Rightarrow> 'a\<times>'a \<Rightarrow> bool" (infix "\<leadsto>\<^sub>L" 60) where
  "lup \<equiv> \<lambda>(a,f) (a',f'). \<forall>n c. (n_valid a n \<and> n_equiv n a (f \<cdot> c)) 
    \<longrightarrow> (n_valid a' n \<and> n_equiv n a' (f' \<cdot> c))"

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

lemma incl_refl[simp]: "incl a a"
proof (unfold incl_def)
  have "a = (a\<cdot>\<epsilon>)"
    by (auto simp: \<epsilon>_right_id ofe_class.ofe_refl)
  then show "\<exists>c. a = (a \<cdot> c)" by auto
qed

lemma \<epsilon>_n_valid: "n_valid \<epsilon> n" by (simp add: \<epsilon>_valid[unfolded valid_def])

lemma n_incl_trans: "\<lbrakk>n_incl n a b; n_incl n b c\<rbrakk> \<Longrightarrow> n_incl n a c"
  apply (auto simp: n_incl_def) using ofe_trans op_ne
  by (smt (verit, ccfv_threshold) dual_order.refl local.camera_assoc local.op_equiv_subst)

lemma n_incl_op: "\<lbrakk>n_incl n a b; n_incl n x y\<rbrakk> \<Longrightarrow> n_incl n (a\<cdot>x) (b\<cdot>y)"
proof -
  assume assms: "n_incl n a b" "n_incl n x y"
  then obtain c z where " n_equiv n b (a\<cdot>c)" "n_equiv n y (x\<cdot>z)" unfolding n_incl_def by blast
  from op_ne[OF this HOL.refl HOL.refl] have "n_equiv n (b\<cdot>y) (a\<cdot>x\<cdot>(c\<cdot>z))" using camera_comm camera_assoc
    by simp
  then show ?thesis unfolding n_incl_def by blast
qed
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

lemma total_dicrete_update: "(x::'a::{dcamera,total_camera})\<leadsto>y \<longleftrightarrow> (\<forall>z. valid (x \<cdot> z) \<longrightarrow> valid (y \<cdot> z))"
  apply (subst total_update)
  apply (auto simp: valid_def)
  using dcamera_valid_iff by blast

definition dcamera_val :: "'a::camera \<Rightarrow> bool" where
  "dcamera_val v \<equiv> discrete_val v \<and> (n_valid v 0 \<longrightarrow> valid v)"

lemma dcamera_dcamera_val [simp]: "dcamera_val (x::'a::dcamera)"
  by (simp add: dcamera_val_def d_valid discrete_val_def d_equiv d_eq)

text \<open>Discrete Unital Camera\<close>
class ducamera = dcamera + ucamera
class core_id_ucamera = core_id + ucamera

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

subsubsection \<open> Option type \<close>
fun option_op :: "('a::camera) option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "option_op (Some a) (Some b) = Some (op a b)"
| "option_op (Some a) (None) = Some a"
| "option_op (None) (Some a) = Some a"  
| "option_op None None = None"

lemma option_opE: "option_op x y = None \<Longrightarrow> x=None \<and> y=None"
  by (induction x y rule: option_op.induct) auto

lemma option_op_none_unit [simp]: "option_op None x = x" "option_op x None = x"
  apply (cases x) apply auto apply (cases x) by auto

lemmas op_ex2 = option.exhaust[case_product option.exhaust]
lemmas op_ex3 = option.exhaust[case_product op_ex2]
lemmas op_ex4 = op_ex3[case_product option.exhaust]

lemma option_op_ne: "non_expansive2 option_op"
proof (rule non_expansive2I)
fix x y a b :: "'a option"
fix n
show "n_equiv n x y \<Longrightarrow> n_equiv n a b \<Longrightarrow> n_equiv n (option_op x a) (option_op y b)"
  by (cases x y a b rule: op_ex4) (auto simp: n_equiv_option_def split: option.splits)
qed

instantiation option :: (camera) camera begin
  definition valid_raw_option :: "'a option \<Rightarrow> sprop" where
    "valid_raw_option x = (case x of Some a \<Rightarrow> valid_raw a | None \<Rightarrow> sTrue)"
  definition pcore_option :: "'a option \<Rightarrow> 'a option option" where
    "pcore_option x = (case x of Some a \<Rightarrow> Some (pcore a) | None \<Rightarrow> Some None)"
  definition "op_option \<equiv> option_op"
instance proof
show "non_expansive (valid_raw::'a option \<Rightarrow> sprop)" by (rule non_expansiveI) 
  (auto simp: valid_raw_option_def ofe_refl n_equiv_option_def valid_raw_ne split: option.splits)
next
show "non_expansive (pcore::'a option \<Rightarrow> 'a option option)" 
  by (rule non_expansiveI;auto simp: pcore_option_def ofe_refl pcore_ne n_equiv_option_def split: option.split)
  (meson n_equiv_option_def pcore_ne)+
next
show "non_expansive2 (op::'a option \<Rightarrow> 'a option \<Rightarrow> 'a option)"
  by (simp add: op_option_def option_op_ne)
next
fix a b c :: "'a option"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (cases a; cases b; cases c) (auto simp: op_option_def camera_assoc)
next
fix a b :: "'a option"
show "a \<cdot> b = b \<cdot> a" by (cases a; cases b) (auto simp: op_option_def camera_comm)
next
fix a a' :: "'a option"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a"
  by (cases a; cases a') (auto simp: op_option_def pcore_option_def camera_pcore_id)
next
fix a a' :: "'a option"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a"
  by (cases a; cases a') (auto simp: pcore_option_def camera_pcore_idem)
next
fix a a' b :: "'a option"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (cases a; cases a'; cases b)
  apply (simp_all add: pcore_option_def op_option_def del: option_op_none_unit)
  apply (metis option.exhaust option_op.simps(3) option_op.simps(4))
  apply (metis option_op.simps(4))
  apply (metis option.exhaust option_op.simps(3) option_op.simps(4))
  apply (metis option.distinct(1) option_op.elims)
  by (metis camera_pcore_mono not_Some_eq option.inject option_op.simps(1) option_op.simps(2))
next
fix a b :: "'a option"
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (cases a; cases b) (auto simp: valid_raw_option_def op_option_def camera_valid_op)
next
fix a b c :: "'a option"
fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  apply (cases a b c rule: op_ex3; auto simp: valid_raw_option_def op_option_def n_equiv_option_def)
  using camera_extend by force+
qed
end

lemma option_n_equiv_Some_op: "n_equiv n z (Some x \<cdot> y) \<Longrightarrow> \<exists>z'. z = Some z'"
  apply (cases y)
  by (auto simp: n_equiv_option_def op_option_def)

lemma option_n_incl: "n_incl n o1 o2 \<longleftrightarrow> 
  (o1 = None \<or> (\<exists>x y. o1 = Some x \<and> o2 = Some y \<and> (n_equiv n x y \<or> n_incl n x y)))"
  apply (cases o1; cases o2)
  apply (simp_all add: n_incl_def n_equiv_option_def op_option_def)
  apply (meson ofe_eq_limit option_op.simps(3))
  using option_op.elims apply blast 
  apply (rule iffI)
  apply (metis (no_types, lifting) ofe_sym option.discI option.sel option_op.elims)
  using ofe_sym option_op.simps(1) option_op.simps(2) by blast

lemma unital_option_n_incl: "n_incl n (Some (x::'a::ucamera)) (Some y) \<longleftrightarrow> n_incl n x y"
proof
  assume "n_incl n (Some x) (Some y)"
  then obtain z where z: "n_equiv n (Some y) (Some x \<cdot> z)" by (auto simp: n_incl_def)
  then have "z=Some c \<Longrightarrow> n_equiv n y (x \<cdot> c)" for c by (auto simp: n_equiv_option_def op_option_def)
  moreover from z have "z=None \<Longrightarrow> n_equiv n y (x\<cdot>\<epsilon>)" by (auto simp: n_equiv_option_def op_option_def \<epsilon>_right_id)
  ultimately show "n_incl n x y" unfolding n_incl_def using z apply (cases z) by auto
next
  assume "n_incl n x y"
  then obtain z where "n_equiv n y (x\<cdot>z)" by (auto simp: n_incl_def)
  then have "n_equiv n (Some y) (Some x \<cdot> Some z)" by (auto simp: n_equiv_option_def op_option_def)
  then show "n_incl n (Some x) (Some y)" by (auto simp: n_incl_def)
qed
  
instance option :: (dcamera) dcamera
  apply (standard; auto simp: valid_raw_option_def valid_def split: option.splits)
  using d_valid[simplified valid_def] by blast

instance option :: (core_id) core_id 
  by standard(auto simp: pcore_option_def  pcore_id split: option.splits)

lemma map_option_ne: "non_expansive f \<Longrightarrow> non_expansive (map_option f)"
  by (auto simp: non_expansive_def n_equiv_option_def)

instantiation option :: (camera) ucamera begin
definition "\<epsilon>_option \<equiv> None"
instance 
  by (standard; auto simp: valid_def valid_raw_option_def op_option_def pcore_option_def \<epsilon>_option_def)
end

instance option :: (dcamera) ducamera ..

type_synonym 'a upd = "'a \<Rightarrow> 'a"

text \<open>Locale to denote that a resource type contains a certain camera type. Allows modular proofs.\<close>
locale inG = 
fixes get_cmra :: "gname \<Rightarrow> 'a::ucamera \<Rightarrow> 'b::camera option"
  and upd_cmra :: "gname \<Rightarrow> 'b option upd \<Rightarrow> 'a upd"
assumes 
  get_upd_cmra: "f (get_cmra \<gamma> a) = get_cmra \<gamma> a \<Longrightarrow> upd_cmra \<gamma> f a = a"
  and upd_get_cmra: "get_cmra \<gamma> (upd_cmra \<gamma> f a) = f (get_cmra \<gamma> a)"
  and upd_compose_cmra: "upd_cmra \<gamma> f (upd_cmra \<gamma> g a) = upd_cmra \<gamma> (f o g) a"
  and upd_ne: "n_equiv n (upd_cmra \<gamma> f a) (upd_cmra \<gamma> g b) \<Longrightarrow> n_equiv n (f (get_cmra \<gamma> a)) (g (get_cmra \<gamma> b))"
  and upd_ne2: "\<lbrakk>n_equiv n (f (get_cmra \<gamma> a)) (g (get_cmra \<gamma> b)); n_equiv n a b\<rbrakk> \<Longrightarrow> 
    n_equiv n (upd_cmra \<gamma> f a) (upd_cmra \<gamma> g b)"
  and upd_n_valid: "n_valid (upd_cmra \<gamma> f a) n \<Longrightarrow> n_valid (f (get_cmra \<gamma> a)) n"
  and upd_n_valid2: "\<lbrakk>n_valid (f (get_cmra \<gamma> a)) n; n_valid a n\<rbrakk> \<Longrightarrow> n_valid (upd_cmra \<gamma> f a) n"
  and upd_op: "upd_cmra \<gamma> (\<lambda>_. (f (get_cmra \<gamma> a)) \<cdot> (g (get_cmra \<gamma> b))) (a\<cdot>b) = 
    (upd_cmra \<gamma> f a) \<cdot> (upd_cmra \<gamma> g b)"
  and get_op: "get_cmra \<gamma> (a \<cdot> b) = get_cmra \<gamma> a\<cdot>get_cmra \<gamma> b"
  and get_n_valid: "get_cmra \<gamma> a = x \<Longrightarrow> n_valid a n \<Longrightarrow> n_valid x n"
  and get_valid_op: "\<lbrakk>get_cmra \<gamma> a = y; n_valid (b \<cdot> a) n; n_valid (f x\<cdot>y) n; get_cmra \<gamma> b = x\<rbrakk> \<Longrightarrow> 
    n_valid (upd_cmra \<gamma> f b \<cdot> a) n"
  and get_ne: "n_equiv n a b \<Longrightarrow> n_equiv n (get_cmra \<gamma> a) (get_cmra \<gamma> b)"
  and upd_pcore: "pcore (upd_cmra \<gamma> f a) = Some (case (pcore a) of Some b \<Rightarrow>
    (case (pcore (f (get_cmra \<gamma> a))) of Some y \<Rightarrow> (upd_cmra \<gamma> (\<lambda>_. y) b) | None \<Rightarrow> \<epsilon>) | None \<Rightarrow> \<epsilon>)"
  and get_\<epsilon>: "get_cmra \<gamma> \<epsilon> = None"
  and upd_id_cmra: "upd_cmra \<gamma> id a = a"
  and return_ne_exists: "n_equiv n (upd_cmra \<gamma> (\<lambda>_. Some z) \<epsilon>) a \<Longrightarrow>
    \<exists>y'. a = upd_cmra \<gamma> (\<lambda>_. Some y') \<epsilon>"
begin
  definition put_cmra :: "gname \<Rightarrow> 'a \<Rightarrow> 'b option \<Rightarrow> 'a" where
    "put_cmra \<gamma> a x = upd_cmra \<gamma> (\<lambda>_. x) a"
  
  lemma get_put: "put_cmra \<gamma> a (get_cmra \<gamma> a) = a"
    unfolding put_cmra_def using get_upd_cmra by simp
  lemma put_get: "get_cmra \<gamma> (put_cmra \<gamma> a x) = x"
    unfolding put_cmra_def using upd_get_cmra by auto
  lemma put_put: "put_cmra \<gamma> (put_cmra \<gamma> a y) x = put_cmra \<gamma> a x"
    unfolding put_cmra_def upd_compose_cmra by (simp add: K_record_comp)
  lemma put_ne: "n_equiv n (put_cmra \<gamma> a x) (put_cmra \<gamma> b y) \<Longrightarrow> n_equiv n x y" 
    unfolding put_cmra_def using upd_ne by blast
  lemma put_ne2: "\<lbrakk>n_equiv n x y; n_equiv n a b\<rbrakk> \<Longrightarrow> n_equiv n (put_cmra \<gamma> a x) (put_cmra \<gamma> b y)"
    unfolding put_cmra_def using upd_ne2 by simp
  lemma put_n_valid: "n_valid (put_cmra \<gamma> a x) n \<Longrightarrow> n_valid x n"
    unfolding put_cmra_def using upd_n_valid by blast
  lemma put_n_valid2: "\<lbrakk>n_valid x n; n_valid a n\<rbrakk> \<Longrightarrow> n_valid (put_cmra \<gamma> a x) n"
    unfolding put_cmra_def using upd_n_valid2 by simp
  lemma put_op: "put_cmra \<gamma> (a\<cdot>b) (x \<cdot> y) = (put_cmra \<gamma> a x) \<cdot> (put_cmra \<gamma> b y)"
    unfolding put_cmra_def by (rule upd_op)
  lemma put_incl_get: "n_incl n (put_cmra \<gamma> b (Some c)) a \<Longrightarrow> get_cmra \<gamma> a \<noteq> None"
  proof -
    assume assm: "n_incl n (put_cmra \<gamma> b (Some c)) a"
    then have "\<exists>d. n_equiv n a (upd_cmra \<gamma> (\<lambda>_. Some c) b \<cdot> d)" 
      by (simp add: n_incl_def put_cmra_def)
    then obtain d where "n_equiv n a (upd_cmra \<gamma> (\<lambda>_. Some c) b \<cdot> d)" by blast
    then have "n_equiv n (upd_cmra \<gamma> id a) (upd_cmra \<gamma> (\<lambda>_. Some c) b \<cdot> upd_cmra \<gamma> id d)" 
      by (simp add: upd_id_cmra)
    then have "n_equiv n (upd_cmra \<gamma> id a) (upd_cmra \<gamma> (\<lambda>_. Some c \<cdot> get_cmra \<gamma> d) (b \<cdot> d))" 
      unfolding upd_op[symmetric] id_def by assumption
    from upd_ne[OF this] have "n_equiv n (get_cmra \<gamma> a) (Some c \<cdot> get_cmra \<gamma> d)" 
      by (simp add: id_def)
    then show ?thesis using option_opE by (auto simp: n_equiv_option_def op_option_def)
  qed  

  lemma put_pcore: "pcore (put_cmra \<gamma> a x) = Some (case (pcore a) of Some b \<Rightarrow>
    (case (pcore x) of Some y \<Rightarrow> (put_cmra \<gamma> b y) | None \<Rightarrow> \<epsilon>) | None \<Rightarrow> \<epsilon>)"
    unfolding put_cmra_def upd_pcore by simp

  (* A monadic return constructor for a resource that only contains the given camera object. *)
  definition return_cmra :: "gname \<Rightarrow> 'b \<Rightarrow> 'a" where
    "return_cmra \<gamma> x = put_cmra \<gamma> \<epsilon> (Some x)"

  lemma return_ne: "n_equiv n (return_cmra \<gamma> x) (return_cmra \<gamma> y) \<longleftrightarrow> n_equiv n x y"
    apply (auto simp: return_cmra_def)
    apply (drule put_ne) apply (simp add: n_equiv_option_def)
    apply (rule put_ne2[OF _ ofe_refl]) by (simp add: n_equiv_option_def)
  lemma return_ne2: "n_equiv n (return_cmra \<gamma> x) y \<Longrightarrow> \<exists>y'. y = return_cmra \<gamma> y'"
    apply (auto simp: return_cmra_def put_cmra_def)
    by (rule return_ne_exists)
  lemma return_get: "get_cmra \<gamma> (return_cmra \<gamma> x) = Some x"
    by (simp add: return_cmra_def put_get)
  lemma return_n_valid: "n_valid (return_cmra \<gamma> x) n \<longleftrightarrow> n_valid x n"
    apply (auto simp: return_cmra_def)
    apply (frule put_n_valid) apply (simp add: valid_raw_option_def)
    apply (rule put_n_valid2[OF _ \<epsilon>_n_valid]) by (simp add: valid_raw_option_def)
  lemma return_op: "return_cmra \<gamma> (x \<cdot> y) = (return_cmra \<gamma> x) \<cdot> (return_cmra \<gamma> y)" 
    by (simp add: return_cmra_def \<epsilon>_left_id put_op[symmetric] op_option_def)
  lemma return_incl_get: "n_incl n (return_cmra \<gamma> x) a \<Longrightarrow> get_cmra \<gamma> a \<noteq> None"
    by (simp add: return_cmra_def put_incl_get)
  lemma return_pcore: "pcore (return_cmra \<gamma> x) = Some (case (pcore x) of Some y \<Rightarrow> (return_cmra \<gamma> y) | None \<Rightarrow> \<epsilon>)"
    unfolding return_cmra_def
    apply (auto simp add: put_pcore)
    apply (simp add: \<epsilon>_pcore pcore_option_def) apply (cases "pcore x")
    apply auto apply (subst get_\<epsilon>[symmetric, of \<gamma>]) by (rule get_put)
  lemma return_valid: "valid (return_cmra \<gamma> x) \<longleftrightarrow> valid x"
    by (auto simp: valid_def return_n_valid)

  lemma get_n_valid2: "n_valid a n \<Longrightarrow> n_valid (get_cmra \<gamma> a) n"
    apply (cases "get_cmra \<gamma> a") apply (simp add: valid_raw_option_def) 
    by (frule get_n_valid, assumption, simp add: valid_raw_option_def)
  lemma get_none_op: "get_cmra \<gamma> a = None \<Longrightarrow> get_cmra \<gamma> (a \<cdot> b) = get_cmra \<gamma> b" 
    by (auto simp: get_op op_option_def)
   
  lemma get_valid_op2: "\<lbrakk>get_cmra \<gamma> a = y; n_valid a n; n_valid (Some x\<cdot>y) n\<rbrakk> \<Longrightarrow> 
    n_valid (return_cmra \<gamma> x \<cdot> a) n"
    unfolding return_cmra_def put_cmra_def
    apply (erule get_valid_op)
    apply (simp add: \<epsilon>_left_id)
    apply assumption
    by simp    

  lemma incl_return_get: "n_incl n (return_cmra \<gamma> x) a \<longleftrightarrow> n_incl n (Some x) (get_cmra \<gamma> a)"
    apply (cases "get_cmra \<gamma> a")
    apply (auto simp: n_incl_def n_equiv_option_def op_option_def return_cmra_def dest: option_opE)
    apply (metis n_incl_def put_incl_get return_cmra_def)
    proof -
      fix b c
      assume assms: "get_cmra \<gamma> a = Some b" "n_equiv n a (put_cmra \<gamma> \<epsilon> (Some x) \<cdot> c)"
      with get_ne have "n_equiv n (Some b) (get_cmra \<gamma> (put_cmra \<gamma> \<epsilon> (Some x) \<cdot> c))" by metis
      with get_op put_get have "n_equiv n (Some b) (Some x \<cdot> get_cmra \<gamma> c)"
        by simp
      then have "\<exists>y'. option_op (Some x) (get_cmra \<gamma> c) = Some y' \<and> n_equiv n b y'"
        by (auto simp: op_option_def n_equiv_option_def)
      then show "\<exists>c y'. option_op (Some x) c = Some y' \<and> n_equiv n b y'" by blast
    next
      fix b c y'
      assume assms: "get_cmra \<gamma> a = Some b" "option_op (Some x) c = Some y'" "n_equiv n b y'"
      then have "c=Some c' \<Longrightarrow> n_equiv n a (put_cmra \<gamma> \<epsilon> (Some x) \<cdot> put_cmra \<gamma> a (Some c'))" for c'
        apply (auto simp: put_op[symmetric] \<epsilon>_left_id op_option_def)
        by (metis get_put n_equiv_option_def ofe_refl put_ne2)
      moreover from assms have "c=None \<Longrightarrow> n_equiv n a (put_cmra \<gamma> \<epsilon> (Some x) \<cdot> put_cmra \<gamma> a None)"
        apply (auto simp: put_op[symmetric] \<epsilon>_left_id op_option_def)
        by (metis get_put n_equiv_option_def ofe_refl put_ne2)
      ultimately show "\<exists>c. n_equiv n a (put_cmra \<gamma> \<epsilon> (Some x) \<cdot> c)" by (cases c) auto
   qed

  lemma upd_id_map_option_none: "get_cmra \<gamma> x = None \<Longrightarrow> upd_cmra \<gamma> (map_option f) x = x"
    by (rule get_upd_cmra,simp)

  lemma upd_partial_ne: "\<lbrakk>n_equiv n x (y\<cdot>z); n_equiv n (f (get_cmra \<gamma> x)) (g (get_cmra \<gamma> y) 
    \<cdot> (get_cmra \<gamma> z))\<rbrakk> \<Longrightarrow> n_equiv n (upd_cmra \<gamma> f x) (upd_cmra \<gamma> g y \<cdot> z)"
  by (smt (verit, del_insts) get_put inG.put_cmra_def inG_axioms upd_ne2 upd_op)
end
end