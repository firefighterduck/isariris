theory CoreStructures
imports OFEs
begin

section \<open> Core Structures \<close>
text \<open> This section introduces the concepts of cameras, resource algebras and related structures. \<close>
    
(* Non-expansive functions, i.e. equivalence persisting functions from one OFE to another. *)
locale non_expansive =
  fixes ne :: "'a::ofe \<Rightarrow> 'b::ofe"
  assumes ne_def: "(x,y) \<in> n_equiv n \<Longrightarrow> (ne x, ne y) \<in> n_equiv n"

(* Resource algebra *)
locale ra =
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
locale camera =
  ofe_m: ofe eq_m + valid_raw: non_expansive valid_raw + core: non_expansive core
    + comp: non_expansive comp
  for eq_m :: "nat \<Rightarrow> ('a::ofe\<times>'a) set" and valid_raw :: "'a \<Rightarrow> sprop" and core :: "'a \<Rightarrow> 'a option" 
    and comp :: "('a\<times>'a) \<Rightarrow> 'a" +
  assumes camera_assoc: "comp (comp (a,b),c) = comp (a,comp (b,c))"
    and camera_comm: "comp (a,b) = comp (b,a)"
    and camera_core_id: "\<exists>a'. core a = Some a' \<Longrightarrow> comp (the (core a),a) = a"
    and camera_core_idem: "\<exists>a'. core a = Some a' \<Longrightarrow> core (the (core a)) = core a"
    and camera_core_mono: "\<lbrakk>\<exists>a'. core a = Some a'; \<exists>c. b=comp (a,c)\<rbrakk> \<Longrightarrow> 
      (\<exists>b'. (core b = Some b') \<and> (\<exists>c. (the (core b)) = comp (the (core a),c)))"
    and camera_valid_op: "valid_raw (comp (a,b)) \<le> valid_raw a"
    and camera_extend: "\<lbrakk>n \<le> valid_raw a; (a,comp (b1,b2)) \<in> n_equiv n\<rbrakk> \<Longrightarrow>
      \<exists>c1 c2. (a=comp (c1,c2) \<and> (c1,b2) \<in> n_equiv n \<and> (c2,b2) \<in> n_equiv n)"
    
definition (in camera) valid :: "'a \<Rightarrow> bool" where
  "valid a = (\<forall>n. n \<le> valid_raw a)"

locale total_camera =
  camera eq_m valid_raw core comp
    for eq_m and valid_raw and core and comp +
  fixes \<epsilon> :: 'a
  assumes \<epsilon>_valid: "valid \<epsilon>"
    and \<epsilon>_left_id: "comp (\<epsilon>,a) = a"
    and \<epsilon>_core: "core \<epsilon> = Some \<epsilon>"

definition (in total_camera) total_core :: "'a \<Rightarrow> 'a" where
  "total_core a = (case core a of Some a \<Rightarrow> a | None \<Rightarrow> \<epsilon>)"  
end