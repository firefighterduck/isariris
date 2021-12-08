theory CoreStructures
imports OFEs
begin

section \<open> Core Structures \<close>
text \<open> This section introduces the concepts of cameras, resource algebras and related structures. \<close>
    
(* Non-expansive functions, i.e. equivalence persisting functions from one OFE to another. *)
typedef (overloaded) ('a::ofe,'b::ofe) non_expansive = 
  "{ne::'a\<Rightarrow>'b. \<forall>(x::'a) y n. n_equiv n x y \<longrightarrow> n_equiv n (ne x) (ne y)}"
proof
  fix b :: 'b
  define ne where "ne = (\<lambda>_::'a. b)"
  hence "\<forall>x y n. n_equiv n x y \<longrightarrow> n_equiv n (ne x) (ne y)" by (simp add: ofe_refl)
  then show "ne \<in> {ne. \<forall>x y n. n_equiv n x y \<longrightarrow> n_equiv n (ne x) (ne y)}" by blast
qed
setup_lifting type_definition_non_expansive

lemma ne_sprop_weaken: 
  "\<lbrakk>n_equiv n x y; m\<le>n; Rep_sprop (Rep_non_expansive P x) n\<rbrakk> \<Longrightarrow> Rep_sprop (Rep_non_expansive P y) m"
  using Rep_non_expansive Rep_sprop n_equiv_sprop_def by fastforce

(* Resource algebra *)
class ra =
  fixes valid :: "'a \<Rightarrow> bool"
    and core :: "'a \<Rightarrow> 'a option"
    and comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes ra_assoc: "comp (comp a b) c = comp a (comp b c)"
    and ra_comm: "comp a b = comp b a"
    and ra_core_id: "\<exists>a'. core a = Some a' \<Longrightarrow> comp (the (core a)) a = a"
    and ra_core_idem: "\<exists>a'. core a = Some a' \<Longrightarrow> core (the (core a)) = core a"
    and ra_core_mono: "\<lbrakk>\<exists>a'. core a = Some a'; \<exists>c. b=comp a c\<rbrakk> \<Longrightarrow> 
      (\<exists>b'. (core b = Some b') \<and> (\<exists>c. (the (core b)) = comp (the (core a)) c))"
    and ra_valid_op: "valid (comp a b) \<Longrightarrow> valid a"

(* Camera, a more general notion of resource algebras based on an OFE. *)
class camera = ofe +
  fixes valid_raw :: "(('a::ofe),sprop) non_expansive" and core :: "('a,'a option) non_expansive" 
    and comp :: "(('a\<times>'a),'a) non_expansive"
  assumes camera_assoc: 
      "Rep_non_expansive comp (Rep_non_expansive comp (a,b),c) 
      = Rep_non_expansive comp (a,Rep_non_expansive comp (b,c))"
    and camera_comm: 
      "Rep_non_expansive comp (a,b) = Rep_non_expansive comp (b,a)"
    and camera_core_id: 
      "\<exists>a'. Rep_non_expansive core a = Some a' 
      \<Longrightarrow> Rep_non_expansive comp (the (Rep_non_expansive core a),a) = a"
    and camera_core_idem: 
      "\<exists>a'. Rep_non_expansive core a = Some a' 
      \<Longrightarrow> Rep_non_expansive core (the (Rep_non_expansive core a)) = Rep_non_expansive core a"
    and camera_core_mono: 
      "\<lbrakk>\<exists>a'. Rep_non_expansive core a = Some a'; \<exists>c. b=Rep_non_expansive comp (a,c)\<rbrakk> \<Longrightarrow> 
      (\<exists>b'. (Rep_non_expansive core b = Some b') 
      \<and> (\<exists>c. (the (Rep_non_expansive core b)) = Rep_non_expansive comp (the (Rep_non_expansive core a),c)))"
    and camera_valid_op: 
      "Rep_sprop (Rep_non_expansive valid_raw (Rep_non_expansive comp (a,b))) n 
      \<Longrightarrow> Rep_sprop (Rep_non_expansive valid_raw a) n"
    and camera_extend: 
      "\<lbrakk>Rep_sprop (Rep_non_expansive valid_raw a) n; n_equiv n a (Rep_non_expansive comp (b1,b2))\<rbrakk> \<Longrightarrow>
      \<exists>c1 c2. (a=Rep_non_expansive comp (c1,c2) \<and> n_equiv n c1 b1 \<and> n_equiv n c2 b2)"
begin
definition rep_valid_raw :: "'a \<Rightarrow> sprop" where  "rep_valid_raw = Rep_non_expansive valid_raw"
definition valid_n :: "'a \<Rightarrow> nat \<Rightarrow> bool" where "valid_n x = Rep_sprop (rep_valid_raw x)"
definition rep_core :: "'a \<Rightarrow> 'a option" where  "rep_core = Rep_non_expansive core"
definition rep_comp :: "('a\<times>'a) \<Rightarrow> 'a" where  "rep_comp = Rep_non_expansive comp"

definition valid :: "'a \<Rightarrow> bool" where
  "valid a = (\<forall>n. valid_n a n)"

definition incl :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "incl a b = (\<exists>c. b = rep_comp (a,c))"

definition n_incl :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "n_incl n a b = (\<exists>c. n_equiv n b (rep_comp (a,c)))"

(* Frame-preserving update *)
definition fup :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<leadsto>" 50) where
  "a\<leadsto>B \<equiv> (\<forall>x::'a. valid a \<longrightarrow> valid (rep_comp (a,x)) \<longrightarrow> (\<exists>b\<in>B. valid (rep_comp (b,x))))"

(* Auxiliary camera lemmas *)
lemma camera_n_incl_le: "\<lbrakk>n_incl n x y; m\<le>n\<rbrakk> \<Longrightarrow> n_incl m x y"
  by (auto simp: n_incl_def rep_comp_def) (meson ofe_class.ofe_mono)

lemma comp_equiv: "\<lbrakk>n_equiv n x y; n_equiv n a b\<rbrakk> \<Longrightarrow> n_equiv n (rep_comp (x,a)) (rep_comp (y,b))"
proof -
  assume "n_equiv n x y" "n_equiv n a b"
  hence "n_equiv n (x,a) (y,b)" by simp
  hence "n_equiv n (Rep_non_expansive comp (x,a)) (Rep_non_expansive comp (y,b))" 
    using Rep_non_expansive by blast
  thus "n_equiv n (rep_comp (x,a)) (rep_comp (y,b))" using rep_comp_def by simp
qed  

lemma comp_equiv_subst: 
  "\<lbrakk>n_equiv n a (rep_comp (b,c)); n_equiv m b d; n\<le>m\<rbrakk> \<Longrightarrow> n_equiv n a (rep_comp (d,c))"
  by (meson comp_equiv ofe_class.ofe_mono ofe_class.ofe_refl ofe_class.ofe_trans)

lemma valid_comp_comp_weaken: "\<lbrakk>n_equiv n x (rep_comp (y,z)); valid_n (rep_comp (x,x')) n\<rbrakk> 
  \<Longrightarrow> valid_n (rep_comp (rep_comp (y,z),x')) n"
proof -
  assume assm1: "n_equiv n x (rep_comp (y,z))" 
  assume assm2: "valid_n (rep_comp (x,x')) n"
  from assm1 have "n_equiv n (rep_comp (x,x')) (rep_comp (rep_comp (y,z),x'))" 
    by (simp add: ofe_class.ofe_refl comp_equiv)
    from ne_sprop_weaken[OF this, of n, simplified, OF assm2[simplified valid_n_def rep_valid_raw_def]]
  show "valid_n (rep_comp (rep_comp (y,z),x')) n" unfolding valid_n_def rep_valid_raw_def .
qed

lemma valid_n_incl_subst: "\<lbrakk>n_incl n a b; valid_n (rep_comp (b,c)) m; m\<le>n\<rbrakk> 
  \<Longrightarrow> valid_n (rep_comp (a,c)) m"
  using n_incl_def rep_comp_def valid_n_def
  by (smt (verit, ccfv_threshold) camera_assoc camera_comm camera_valid_op ofe_class.ofe_mono rep_valid_raw_def valid_comp_comp_weaken)
  
lemma incl_comp_extend: "incl a b \<Longrightarrow> incl a (rep_comp (b,c))"
  by (auto simp: incl_def rep_comp_def camera_assoc)
lemma n_incl_comp_extend: "n_incl n a (rep_comp (a,c))"
  by (meson n_incl_def ofe_class.ofe_eq_limit)
lemma n_incl_extend: "\<lbrakk>n_incl n a b; m\<le>n\<rbrakk> \<Longrightarrow> n_incl m (rep_comp (a,c)) (rep_comp (b,c))"
  using n_incl_def rep_comp_def
  by (smt (verit, ccfv_threshold) comp_equiv_subst camera_assoc camera_comm ofe_class.ofe_refl)
end
  
class total_camera = camera +
  fixes \<epsilon> :: "'a::camera"
  assumes \<epsilon>_valid: "valid \<epsilon>"
    and \<epsilon>_left_id: "rep_comp (\<epsilon>,a) = a"
    and \<epsilon>_core: "rep_core \<epsilon> = Some \<epsilon>"
begin
definition total_core :: "'a \<Rightarrow> 'a" where
  "total_core a = (case rep_core a of Some a \<Rightarrow> a | None \<Rightarrow> \<epsilon>)"

lemma \<epsilon>_total[simp]: "total_core \<epsilon> = \<epsilon>"
  by (auto simp: total_core_def \<epsilon>_core )

lemma total_n_inclI: "n2\<le>n1 \<Longrightarrow> n_equiv n1 x1 x2 \<Longrightarrow> n_incl n2 x1 (x2::'a)"
proof (unfold camera_class.n_incl_def; standard)
  assume "n2\<le>n1" "n_equiv n1 x1 x2"
  then have "n_equiv n2 x1 x2" by (rule ofe_class.ofe_mono)
  then have "n_equiv n2 (rep_comp (x1,\<epsilon>)) x2" 
    by (metis camera_class.camera_comm camera_class.rep_comp_def \<epsilon>_left_id)
  then show "n_equiv n2 x2 (rep_comp (x1, \<epsilon>))" by (simp add: ofe_class.ofe_sym)
qed
end
end