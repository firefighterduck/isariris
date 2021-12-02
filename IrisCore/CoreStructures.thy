theory CoreStructures
imports OFEs
begin

section \<open> Core Structures \<close>
text \<open> This section introduces the concepts of cameras, resource algebras and related structures. \<close>
    
(* Non-expansive functions, i.e. equivalence persisting functions from one OFE to another. *)
typedef (overloaded) ('a::ofe,'b::ofe) non_expansive = 
  "{ne::'a\<Rightarrow>'b. \<forall>(x::'a) y n. (x,y) \<in> n_equiv n \<longrightarrow> (ne x, ne y) \<in> n_equiv n }"
proof
  fix b :: 'b
  define ne where "ne = (\<lambda>_::'a. b)"
  hence "\<forall>x y n. (x, y) \<in> n_equiv n \<longrightarrow> (ne x, ne y) \<in> n_equiv n" by (simp add: ofe_refl)
  then show "ne \<in> {ne. \<forall>x y n. (x, y) \<in> n_equiv n \<longrightarrow> (ne x, ne y) \<in> n_equiv n}" by blast
qed

setup_lifting type_definition_non_expansive

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
      "\<lbrakk>Rep_sprop (Rep_non_expansive valid_raw a) n; (a,Rep_non_expansive comp (b1,b2)) \<in> n_equiv n\<rbrakk> \<Longrightarrow>
      \<exists>c1 c2. (a=Rep_non_expansive comp (c1,c2) \<and> (c1,b2) \<in> n_equiv n \<and> (c2,b2) \<in> n_equiv n)"
begin
definition rep_valid_raw :: "'a \<Rightarrow> sprop" where  "rep_valid_raw = Rep_non_expansive valid_raw"      
definition rep_core :: "'a \<Rightarrow> 'a option" where  "rep_core = Rep_non_expansive core"
definition rep_comp :: "('a\<times>'a) \<Rightarrow> 'a" where  "rep_comp = Rep_non_expansive comp"

definition valid :: "'a \<Rightarrow> bool" where
  "valid a = (\<forall>n. Rep_sprop (rep_valid_raw a) n)"

definition incl :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "incl a b = (\<exists>c. b = rep_comp (a,c))"

definition n_incl :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "n_incl n a b = (\<exists>c. (b, rep_comp (a,c)) \<in> n_equiv n)"
end
  
class total_camera = camera +
  fixes \<epsilon> :: "'a::ofe"
  assumes \<epsilon>_valid: "valid \<epsilon>"
    and \<epsilon>_left_id: "rep_comp (\<epsilon>,a) = a"
    and \<epsilon>_core: "rep_core \<epsilon> = Some \<epsilon>"

definition (in total_camera) total_core :: "'a \<Rightarrow> 'a" where
  "total_core a = (case rep_core a of Some a \<Rightarrow> a | None \<Rightarrow> \<epsilon>)"

subsection \<open> Uniform Predicates \<close>
(* First monotone, non-expansive functions *)  
typedef (overloaded) 'm mon_ne = "{\<Phi>::('m::camera,sprop) non_expansive. 
  \<forall>n a b. n_incl n a b \<longrightarrow> n_subseteq n (Rep_non_expansive \<Phi> a) (Rep_non_expansive \<Phi> b)}"
proof
  fix s :: sprop
  define mon_ne where "mon_ne = Abs_non_expansive (\<lambda>_::'m. s)"
  then have  "\<forall>n a b. n_incl n a b \<longrightarrow> n_subseteq n (Rep_non_expansive mon_ne a) (Rep_non_expansive mon_ne b)"
    by (simp add: Abs_non_expansive_inverse[of "(\<lambda>_. s)"] ofe_refl n_subseteq_def)
  thus "mon_ne \<in> {\<Phi>. \<forall>n a b. n_incl n a b \<longrightarrow> n_subseteq n (Rep_non_expansive \<Phi> a) (Rep_non_expansive \<Phi> b)}"
   by simp  
qed
setup_lifting type_definition_mon_ne
  
definition rep_mon :: "'a mon_ne \<Rightarrow> 'a::camera \<Rightarrow> sprop" where 
  "rep_mon = Rep_non_expansive \<circ> Rep_mon_ne"

definition abs_mon :: "('a::camera \<Rightarrow> sprop) \<Rightarrow> 'a mon_ne" where
  "abs_mon = Abs_mon_ne \<circ> Abs_non_expansive"  
  
definition mon_ne_equiv :: "('a::camera) mon_ne \<Rightarrow> 'a mon_ne \<Rightarrow> bool" where
  "mon_ne_equiv x y = (\<forall>m a. Rep_sprop (rep_valid_raw a) m 
    \<longrightarrow> (Rep_sprop (rep_mon x a) m \<longleftrightarrow> Rep_sprop (rep_mon y a) m))"

(* Then the actual uniform predicate *)
quotient_type (overloaded) 'b uprop = "('b::camera) mon_ne" / mon_ne_equiv
  by (simp add: mon_ne_equiv_def equivp_reflp_symp_transp reflp_def symp_def transp_def)

instantiation uprop :: (camera) cofe begin
  lift_definition lim_uprop :: "(nat \<Rightarrow> 'a uprop) \<Rightarrow> 'a uprop" is
    "\<lambda>c. abs_mon (\<lambda>x. Abs_sprop (\<lambda>n. \<forall>n'\<le>n. Rep_sprop (rep_valid_raw x) n' 
      \<longrightarrow> Rep_sprop (rep_mon (c n') x) n ))"
  sorry (* This is a direct translation from the Coq formalization, so it should hold. *)
    
  lift_definition n_equiv_uprop :: "nat \<Rightarrow> ('a uprop\<times>'a uprop) set" is
    "\<lambda>n. {(x,y) | x y. \<forall>m\<le>n. \<forall>a. 
      Rep_sprop (rep_valid_raw a) m \<longrightarrow> (Rep_sprop (rep_mon x a) m \<longleftrightarrow> Rep_sprop (rep_mon y a) m)}" .

  lift_definition ofe_eq_uprop :: "'a uprop \<Rightarrow> 'a uprop \<Rightarrow> bool" is "\<lambda>x y. mon_ne_equiv x y" 
    unfolding mon_ne_equiv_def by auto
instance sorry
end
end