theory OFEs
imports Main
begin

section \<open> Ordered family of equivalences \<close>
text \<open> The definition of OFEs, COFEs and instances of those. \<close>

subsection \<open> OFE \<close>
class ofe =
  fixes n_equiv :: "nat \<Rightarrow> ('a\<times>'a) set"
    and ofe_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (* Allow for custom equality *)
  assumes ofe_refl: "(x,x) \<in> n_equiv n"
    and ofe_sym: "(x,y) \<in> n_equiv n \<longleftrightarrow> (y,x) \<in> n_equiv n"
    and ofe_trans: "\<lbrakk>(x,y) \<in> n_equiv n; (y,z) \<in> n_equiv n\<rbrakk> \<Longrightarrow> (x,z) \<in> n_equiv n"
    and ofe_mono: "m\<le>n \<Longrightarrow> n_equiv n \<subseteq> n_equiv m"
    and ofe_limit: "(ofe_eq x y) \<longleftrightarrow> (\<forall>n. (x,y) \<in> n_equiv n)"
    
(* Step indexed propositions. They are defined to hold for all steps below a maximum. *)
typedef sprop = "{s::nat\<Rightarrow>bool. \<forall>n m. m\<le>n \<longrightarrow> s n \<longrightarrow> s m}"
proof
  define s :: "nat\<Rightarrow>bool" where "s = (\<lambda>_. True)"
  thus "s \<in> {s::nat\<Rightarrow>bool. \<forall>n m. m\<le>n \<longrightarrow> s n \<longrightarrow> s m}" by simp
qed
setup_lifting type_definition_sprop

instantiation sprop :: ofe begin
  definition n_equiv_sprop :: "nat \<Rightarrow> (sprop\<times>sprop) set" where
    "n_equiv_sprop n = {(x,y) | x y. \<forall>m\<le>n. Rep_sprop x m \<longleftrightarrow> Rep_sprop y m}"
  definition ofe_eq_sprop :: "sprop \<Rightarrow> sprop \<Rightarrow> bool" where
    "ofe_eq_sprop x y = (\<forall>n. (Rep_sprop x n) \<longleftrightarrow> (Rep_sprop y n))"  
instance by (standard, unfold n_equiv_sprop_def ofe_eq_sprop_def) auto 
end

lift_definition n_subseteq :: "nat \<Rightarrow> sprop \<Rightarrow> sprop \<Rightarrow> bool" is
  "\<lambda>n X Y. \<forall>m\<le>n. X m \<longrightarrow> Y m" .

instantiation option :: (ofe) ofe begin
  definition n_equiv_option :: "nat \<Rightarrow> ('a option\<times>'a option) set" where
  "n_equiv_option n = 
    {(x,y) |x y. (\<exists>x' y'. x=Some x'\<and>y=Some y'\<and>(x',y')\<in>n_equiv n) \<or> x=None\<and>y=None}"
  definition ofe_eq_option where 
    "ofe_eq_option x y \<equiv> (x=None\<and>y=None)\<or>(\<exists>x' y'. x=Some x'\<and>y=Some y'\<and>(ofe_eq x' y'))"
instance proof (standard)
  fix x y
  show "(ofe_eq (x::'a option) y) \<longleftrightarrow> (\<forall>n. (x, y) \<in> n_equiv n)"
  by (auto simp: n_equiv_option_def ofe_refl ofe_eq_option_def) (metis ofe_limit option.sel)+
next 
  fix x y n
  show "((x::'a option,y) \<in> n_equiv n) \<longleftrightarrow> ((y,x) \<in> n_equiv n)"
    using ofe_sym by (auto simp: n_equiv_option_def)+
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
  fun ofe_eq_prod :: "'a\<times>'b \<Rightarrow> 'a\<times>'b \<Rightarrow> bool" where 
    "ofe_eq_prod (a1,b1) (a2,b2) = (ofe_eq a1 a2 \<and> ofe_eq b1 b2)"
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
  show "(ofe_eq (x::('a\<times>'b)) y) \<longleftrightarrow> (\<forall>n. (x,y)\<in>n_equiv n)"
  apply (auto simp: n_equiv_prod_def)
  apply (meson OFEs.ofe_eq_prod.elims(2) ofe_limit)
  by (metis (full_types) OFEs.ofe_eq_prod.simps ofe_limit prod.inject)
qed (auto simp: n_equiv_prod_def ofe_sym intro: ofe_refl ofe_trans)
end

instantiation unit :: ofe begin
  definition n_equiv_unit :: "nat \<Rightarrow> (unit \<times> unit) set" where
    "n_equiv_unit _ = {((),())}"
  fun ofe_eq_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where "ofe_eq_unit _ _ = True"
instance by (standard, unfold n_equiv_unit_def) auto
end

datatype ('a::ofe) later = Next 'a
instantiation later :: (ofe) ofe begin
  definition n_equiv_later :: "nat \<Rightarrow> ('a later\<times>'a later) set" where
    "n_equiv_later n = {(Next x, Next y) | x y. n=0 \<or> (x,y) \<in> n_equiv (n-1) }"
  fun ofe_eq_later :: "'a later \<Rightarrow> 'a later \<Rightarrow> bool" where 
    "ofe_eq_later (Next a) (Next b) = ofe_eq a b"
instance proof (standard)
  fix x n
  show "(x::'a later,x) \<in> n_equiv n" 
    by (cases n) (auto simp: n_equiv_later_def intro: later.exhaust ofe_refl)
next  
  fix x y n
  show "((x::'a later,y) \<in> n_equiv n) \<longleftrightarrow> ((y,x) \<in> n_equiv n)"
    apply (cases n) apply (auto simp: n_equiv_later_def intro: later.exhaust)
    using ofe_sym apply blast using ofe_sym by blast
next
  fix x y n z
  show "(x::'a later,y) \<in> n_equiv n \<Longrightarrow> (y,z) \<in> n_equiv n \<Longrightarrow> (x,z) \<in> n_equiv n"
    by (cases n) (auto simp: n_equiv_later_def intro: later.exhaust ofe_trans)
next
  fix m n
  show "m \<le> n \<Longrightarrow> (n_equiv::nat\<Rightarrow>('a later\<times>'a later) set) n \<subseteq> n_equiv m"
    apply (auto simp: n_equiv_later_def) using ofe_mono[of "m-1" "n-1"] by fastforce
next
  fix x y :: "'a later"
  show "(ofe_eq x y) \<longleftrightarrow> (\<forall>n. (x,y) \<in> n_equiv n)"
    apply (auto simp: n_equiv_later_def intro: later.exhaust ofe_refl)
    apply (meson ofe_eq_later.elims(2) ofe_limit)
    by (metis (full_types) OFEs.ofe_eq_later.simps One_nat_def Zero_not_Suc diff_Suc_1 later.inject ofe_limit)
qed  
end

subsection \<open> COFE \<close>
definition is_chain :: "(nat \<Rightarrow> ('t::ofe)) \<Rightarrow> bool" where
  "is_chain c \<equiv> (\<forall>n m. n\<le>m \<longrightarrow> (c m,c n) \<in> n_equiv n)"

class cofe = ofe +
  fixes lim :: "(nat \<Rightarrow> ('a::ofe)) \<Rightarrow> 'a"
  assumes core_compl: "is_chain (c::(nat\<Rightarrow>'a)) \<Longrightarrow> (lim c,c n) \<in> n_equiv n"
end