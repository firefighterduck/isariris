theory CoreStructures
imports Main
begin

section \<open> Core Structures \<close>
text \<open> This section introduces the concepts of cameras, resource algebras and related structures. \<close>

(* Ordered family of equivalences *)
class ofe =
  fixes n_equiv :: "nat \<Rightarrow> ('a\<times>'a) set"
  assumes ofe_refl: "(x,x) \<in> n_equiv n"
    and ofe_sym: "(x,y) \<in> n_equiv n \<longleftrightarrow> (y,x) \<in> n_equiv n"
    and ofe_trans: "\<lbrakk>(x,y) \<in> n_equiv n; (y,z) \<in> n_equiv n\<rbrakk> \<Longrightarrow> (x,z) \<in> n_equiv n"
    and ofe_mono: "m\<le>n \<Longrightarrow> n_equiv n \<subseteq> n_equiv m"
    and ofe_limit: "(x=y) \<longleftrightarrow> (\<forall>n. (x,y) \<in> n_equiv n)"

(* 
  Step indexed propositions.
  The value is the highest step count for which the proposition holds.
  A value of nat.Max is equivalent to True propositions, 
  whereas a value of 0 is equivalent to False.
*)
type_synonym sprop = nat
instantiation nat :: ofe begin
  definition n_equiv_nat :: "nat \<Rightarrow> (sprop\<times>sprop) set" where
    "n_equiv_nat n = {(x,y) | x y. \<forall>m\<le>n. m\<le>x \<longleftrightarrow> m\<le>y}"
instance
  by (standard, unfold n_equiv_nat_def) (auto, presburger?)
end

instantiation option :: (ofe) ofe begin
  definition n_equiv_option :: "nat \<Rightarrow> ('a option\<times>'a option) set" where
  "n_equiv_option n = 
    {(x,y) |x y. (\<exists>x' y'. x=Some x'\<and>y=Some y'\<and>(x',y')\<in>n_equiv n) \<or> x=None\<and>y=None}"
instance proof (standard) 
  fix x y
  show "((x::'a option) = y) \<longleftrightarrow> (\<forall>n. (x, y) \<in> n_equiv n)"
  by (auto simp: n_equiv_option_def ofe_refl) (metis ofe_limit option.sel)
next 
  fix x y n
  show "((x::'a option,y) \<in> n_equiv n) \<longleftrightarrow> ((y,x) \<in> n_equiv n)"
  apply (auto simp: n_equiv_option_def) using ofe_sym by auto
next
  fix m n
  assume assm: "(m::nat)\<le>n"
  show "\<And>m n. m \<le> n \<Longrightarrow> (n_equiv::nat\<Rightarrow>('a option\<times>'a option) set) n \<subseteq> n_equiv m"
  apply (auto simp: n_equiv_option_def) using ofe_mono by auto
qed (auto simp: n_equiv_option_def intro: ofe_refl ofe_trans)
end

instantiation prod :: (ofe,ofe) ofe begin
  definition n_equiv_prod :: "nat \<Rightarrow> (('a\<times>'b)\<times>('a\<times>'b)) set" where
  "n_equiv_prod n = {((x1,y1),(x2,y2)) | x1 x2 y1 y2. (x1,x2) \<in> n_equiv n \<and> (y1,y2) \<in> n_equiv n}"
instance proof (standard)
  fix x n 
  show "(x::('a\<times>'b),x)\<in>n_equiv n"
    by (auto simp: n_equiv_prod_def) (meson ofe_refl surj_pair)
next
  fix m n
  assume assm: "m\<le>(n::nat)"
  show "(n_equiv:: nat \<Rightarrow> (('a\<times>'b)\<times>('a\<times>'b)) set) n \<subseteq> n_equiv m"
  apply (auto simp: n_equiv_prod_def) using ofe_mono assm by auto
next
  fix x y
  show "((x::('a\<times>'b))=y) \<longleftrightarrow> (\<forall>n. (x,y)\<in>n_equiv n)"
  apply (auto simp: n_equiv_prod_def)
  apply (meson surj_pair ofe_limit)
  by (metis (full_types) ofe_limit prod.inject)
qed (auto simp: n_equiv_prod_def ofe_sym intro: ofe_refl ofe_trans)
end

instantiation unit :: ofe begin
  definition n_equiv_unit :: "nat \<Rightarrow> (unit \<times> unit) set" where
    "n_equiv_unit _ = {((),())}"
instance by (standard, unfold n_equiv_unit_def) auto
end

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