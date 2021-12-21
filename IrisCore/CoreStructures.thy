theory CoreStructures
imports OFEs
begin

section \<open> Core Structures \<close>
text \<open> This section introduces the concepts of cameras, resource algebras and related structures. \<close>
    
(* Non-expansive functions, i.e. equivalence persisting functions from one OFE to another. *)
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
  
lemma sprop_ne: "non_expansive (Rep_sprop P)"
  unfolding non_expansive_def n_equiv_nat_def n_equiv_bool_def using Rep_sprop by simp
  
lemma ne_sprop_weaken: 
  "\<lbrakk>n_equiv n x y; m\<le>n; non_expansive P; Rep_sprop (P x) n\<rbrakk> \<Longrightarrow> Rep_sprop (P y) m"
  using Rep_sprop n_equiv_sprop_def non_expansive_def by blast

lemma ne_sprop_weaken2:
  "\<lbrakk>n_equiv n x y; n_equiv n a b; m\<le>n; non_expansive2 P; Rep_sprop (P x a) n\<rbrakk> \<Longrightarrow> Rep_sprop (P y b) m"
  using Rep_sprop n_equiv_sprop_def non_expansive2_def by fast
  
(* Resource algebra *)
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
    
(* Camera, a more general notion of resource algebras based on an OFE. *)
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

class total_camera = camera +
  assumes total_pcore: "\<exists>b. pcore a = Some b"
begin
definition core :: "'a \<Rightarrow> 'a" where
  "core = the \<circ> pcore"

lemma core_ne: "non_expansive core"
proof (auto simp: non_expansive_def core_def)
  fix x y n
  assume assm: "n_equiv n x y"
  from total_pcore obtain x' y' where "pcore x = Some x'" "pcore y = Some y'" by blast
  with pcore_ne[OF assm this, unfolded n_equiv_option_def]
  show "n_equiv n (the (pcore x)) (the (pcore y))" by simp
qed

lemma camera_core_id: "(core a) \<cdot> a = a"
  and camera_core_idem: "core (core a) = core a"
  and camera_core_mono: "incl a b \<Longrightarrow> incl (core a) (core b)"
  apply (auto simp: core_def camera_pcore_id camera_pcore_idem total_pcore incl_def)
  using camera_pcore_mono total_pcore by fastforce

lemma camera_core_mono_n: "n_incl n a b \<Longrightarrow> n_incl n (core a) (core b)"
  by (metis core_ne local.incl_def local.n_incl_def non_expansiveE camera_core_mono)
end 

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
end

class core_id = camera + assumes pcore_id: "pcore a = Some a"
begin
lemma the_core_id: "the (pcore a) = a" by (simp add: pcore_id)
end

lemma core_id: "core (a::'a::{core_id,total_camera}) = a"
  by (simp add: the_core_id core_def)
  
class dcamera = camera + discrete + assumes d_valid: "n_valid x 0 \<Longrightarrow> valid x"
begin
lemma dcamera_valid_iff: "valid x \<longleftrightarrow> n_valid x n"
by (auto simp: d_valid)(auto simp: valid_def)
end

class ducamera = dcamera + ucamera
end