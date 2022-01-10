theory OFEs
imports Main
begin

section \<open> Ordered family of equivalences \<close>
text \<open> The definition of OFEs, COFEs and instances of those. \<close>

section \<open> OFE \<close>
class ofe =
  fixes n_equiv :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and ofe_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (* Allow for custom equality *)
  assumes ofe_refl: "n_equiv n x x"
    and ofe_sym: "n_equiv n x y \<longleftrightarrow> n_equiv n y x"
    and ofe_trans: "\<lbrakk>n_equiv n x y; n_equiv n y z\<rbrakk> \<Longrightarrow> n_equiv n x z"
    and ofe_mono: "\<lbrakk>m\<le>n; n_equiv n x y\<rbrakk> \<Longrightarrow> n_equiv m x y"
    and ofe_limit: "(ofe_eq x y) \<longleftrightarrow> (\<forall>n. n_equiv n x y)"
    and ofe_eq_eq: "(x=y) \<Longrightarrow> ofe_eq x y"
begin 
lemma  ofe_eq_limit: "(x=y) \<Longrightarrow> (\<forall>n. n_equiv n x y)"
  using ofe_limit ofe_eq_eq by simp  
end

class discrete = ofe + assumes d_equiv: "n_equiv n a b = (a=b)" and d_eq: "ofe_eq a b = (a=b)"

lemma ofe_down_contr: "n_equiv n x y \<longleftrightarrow> (\<forall>m\<le>n. n_equiv m x y)"
  by (auto simp: ofe_trans ofe_sym intro: ofe_mono)

subsection \<open> Simple OFE instances \<close>
subsubsection \<open> Step indexed propositions \<close> 
text \<open>They are defined to hold for all steps below a maximum. \<close>
typedef sprop = "{s::nat\<Rightarrow>bool. \<forall>n m. m\<le>n \<longrightarrow> s n \<longrightarrow> s m}"
proof
  define s :: "nat\<Rightarrow>bool" where "s = (\<lambda>_. True)"
  thus "s \<in> {s::nat\<Rightarrow>bool. \<forall>n m. m\<le>n \<longrightarrow> s n \<longrightarrow> s m}" by simp
qed
setup_lifting type_definition_sprop
lemmas [simp] = Rep_sprop_inverse Rep_sprop_inject
lemmas [simp, intro!] = Rep_sprop[unfolded mem_Collect_eq]

instantiation sprop :: ofe begin
  definition n_equiv_sprop :: "nat \<Rightarrow> sprop \<Rightarrow> sprop \<Rightarrow> bool" where
    "n_equiv_sprop n x y \<equiv> \<forall>m\<le>n. Rep_sprop x m \<longleftrightarrow> Rep_sprop y m"
  definition ofe_eq_sprop :: "sprop \<Rightarrow> sprop \<Rightarrow> bool" where
    "ofe_eq_sprop x y \<equiv> \<forall>n. (Rep_sprop x n) \<longleftrightarrow> (Rep_sprop y n)"
instance by (standard, unfold n_equiv_sprop_def ofe_eq_sprop_def) auto
end

lift_definition sPure :: "bool \<Rightarrow> sprop" is "\<lambda>b _. b" .
lemma sPureId: "Rep_sprop (Abs_sprop ((\<lambda>b _. b) b)) n = b"
  using Abs_sprop_inverse by auto
definition sFalse :: sprop where [simp]: "sFalse \<equiv> sPure False"
definition sTrue :: sprop where [simp]: "sTrue \<equiv> sPure True"
lemmas [simp] = sPure.rep_eq sPureId sPureId[simplified sPure.abs_eq[symmetric]]

lift_definition n_subseteq :: "nat \<Rightarrow> sprop \<Rightarrow> sprop \<Rightarrow> bool" is
  "\<lambda>n X Y. \<forall>m\<le>n. X m \<longrightarrow> Y m" .
lift_definition sprop_conj :: "sprop \<Rightarrow> sprop \<Rightarrow> sprop" (infixl "\<and>\<^sub>s" 60) is 
  "\<lambda>x y. (\<lambda>n. x n \<and> y n)" using conj_forward by simp
lift_definition sprop_disj :: "sprop \<Rightarrow> sprop \<Rightarrow> sprop" (infixl "\<or>\<^sub>s" 60) is
  "\<lambda>x y. (\<lambda>n. x n \<or> y n)" using disj_forward by simp
lift_definition sprop_impl :: "sprop \<Rightarrow> sprop \<Rightarrow> sprop" (infixr "\<longrightarrow>\<^sub>s" 60) is
  "\<lambda>x y. (\<lambda>n. \<forall>m\<le>n. x m \<longrightarrow> y m)" by (meson dual_order.trans)

subsubsection \<open>nat OFE\<close>
instantiation nat :: ofe begin
  definition n_equiv_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "n_equiv_nat \<equiv> \<lambda>_. (=)"
  definition ofe_eq_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "ofe_eq_nat \<equiv> (=)"
instance by standard auto
end
instance nat :: discrete by standard (auto)

subsubsection \<open>bool OFE\<close>
instantiation bool :: ofe begin
  definition n_equiv_bool :: "nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where [simp]: "n_equiv_bool \<equiv> \<lambda>_. (=)"
  definition ofe_eq_bool :: "bool \<Rightarrow> bool \<Rightarrow> bool" where [simp]: "ofe_eq_bool \<equiv> (=)"
instance by standard auto
end
instance bool :: discrete by standard (auto)

subsubsection \<open>option OFE\<close>
instantiation option :: (ofe) ofe begin
  definition n_equiv_option :: "nat \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "n_equiv_option n x y \<equiv> (\<exists>x' y'. x=Some x'\<and>y=Some y'\<and> n_equiv n x' y') \<or> x=None\<and>y=None"
  definition ofe_eq_option where
    "ofe_eq_option x y \<equiv> (x=None\<and>y=None)\<or>(\<exists>x' y'. x=Some x'\<and>y=Some y'\<and>(ofe_eq x' y'))"
instance proof (standard)
  fix x y
  show "(ofe_eq (x::'a option) y) \<longleftrightarrow> (\<forall>n. n_equiv n x y)"
  by (auto simp: n_equiv_option_def ofe_refl ofe_eq_option_def) (metis ofe_limit option.sel)+
next 
  fix x y n
  show "(n_equiv n (x::'a option) y) \<longleftrightarrow> (n_equiv n y x)"
    by (auto simp: n_equiv_option_def ofe_sym)
next
  fix m n x y
  show "\<lbrakk>m \<le> n; (n_equiv::nat\<Rightarrow>'a option\<Rightarrow>'a option\<Rightarrow>bool) n x y\<rbrakk> \<Longrightarrow> n_equiv m x y"
    by (auto simp: n_equiv_option_def ofe_mono)
qed (auto simp: n_equiv_option_def ofe_eq_option_def ofe_eq_eq ofe_refl intro: ofe_trans)
end
instance option :: (discrete) discrete 
proof 
fix a b :: "'a option" fix n
show "n_equiv n a b = (a=b)" by (cases a; cases b) (auto simp: n_equiv_option_def d_equiv)
next
fix a b :: "'a option"
show "ofe_eq a b = (a = b)" by (cases a; cases b) (auto simp: ofe_eq_option_def d_eq)
qed

subsubsection \<open>prod OFE\<close>
instantiation prod :: (ofe,ofe) ofe begin
  fun n_equiv_prod :: "nat \<Rightarrow> ('a\<times>'b) \<Rightarrow> ('a\<times>'b) \<Rightarrow> bool" where
    "n_equiv_prod n (x1,y1) (x2,y2) = (n_equiv n x1 x2 \<and> n_equiv n y1 y2)"
  fun ofe_eq_prod :: "'a\<times>'b \<Rightarrow> 'a\<times>'b \<Rightarrow> bool" where 
    "ofe_eq_prod (a1,b1) (a2,b2) = (ofe_eq a1 a2 \<and> ofe_eq b1 b2)"
instance proof (standard)
  fix x n 
  show "n_equiv n x (x::('a\<times>'b))"
    by (cases x) (auto simp: ofe_refl)
next
  fix m n x y
  assume "m\<le>(n::nat)"
  thus "(n_equiv:: nat\<Rightarrow>('a\<times>'b)\<Rightarrow>('a\<times>'b)\<Rightarrow>bool) n x y \<Longrightarrow> n_equiv m x y"
    by (cases x; cases y) (auto simp: ofe_mono Pair_inject)
next
  fix x y
  show "(ofe_eq (x::('a\<times>'b)) y) \<longleftrightarrow> (\<forall>n. n_equiv n x y)"
    by (cases x; cases y) (auto simp: ofe_limit)
qed (auto simp: ofe_sym ofe_eq_eq intro: ofe_refl ofe_trans)
end
instance prod :: (discrete,discrete) discrete by standard (auto simp: d_equiv d_eq)

subsubsection \<open>unit OFE\<close>
instantiation unit :: ofe begin
  definition n_equiv_unit :: "nat \<Rightarrow> unit \<Rightarrow> unit \<Rightarrow> bool" where
    "n_equiv_unit _ _ _ = True"
  fun ofe_eq_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where "ofe_eq_unit _ _ = True"
instance by (standard, unfold n_equiv_unit_def) auto
end
instance unit :: discrete by standard (auto simp: n_equiv_unit_def)

subsubsection \<open>later type OFE\<close>
text \<open>This type encodes the later modality on a type level.\<close>
datatype ('a::ofe) later = Next (later_car: 'a)
instantiation later :: (ofe) ofe begin
  definition n_equiv_later :: "nat \<Rightarrow> 'a later \<Rightarrow> 'a later \<Rightarrow> bool" where
    "n_equiv_later n x y = (n=0 \<or> n_equiv (n-1) (later_car x) (later_car y))"
  fun ofe_eq_later :: "'a later \<Rightarrow> 'a later \<Rightarrow> bool" where 
    "ofe_eq_later (Next a) (Next b) = ofe_eq a b"
instance proof (standard)
  fix x n
  show "n_equiv n (x::'a later) x" 
    by (cases n; cases x) (auto simp: ofe_refl n_equiv_later_def)
next  
  fix x y n
  show "(n_equiv n (x::'a later) y) \<longleftrightarrow> (n_equiv n y x)"
    by (cases n; cases x; cases y) (auto simp: ofe_limit ofe_sym n_equiv_later_def)
next
  fix x y n z
  show "n_equiv n (x::'a later) y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x z"
    by (cases n; cases x; cases y; cases z) (auto simp: n_equiv_later_def intro: ofe_trans)
next
  fix m n x y
  show "m \<le> n \<Longrightarrow> (n_equiv::nat\<Rightarrow>'a later\<Rightarrow>'a later\<Rightarrow>bool) n x y \<Longrightarrow> n_equiv m x y"
    by (cases m; cases n; cases x; cases y) (auto simp: ofe_mono n_equiv_later_def)
next
  fix x y :: "'a later"
  show "(ofe_eq x y) \<longleftrightarrow> (\<forall>n. n_equiv n x y)"
  apply (cases x; cases y) apply (auto simp: ofe_refl n_equiv_later_def)
  using ofe_limit apply blast using ofe_limit by (metis diff_Suc_Suc diff_zero nat.discI)
next
fix x y :: "'a later"
show "(x=y) \<Longrightarrow> ofe_eq x y" using OFEs.ofe_eq_later.elims(3) ofe_eq_eq by auto
qed
end

subsection \<open> COFE \<close>
typedef (overloaded) 't chain = "{c::(nat \<Rightarrow> 't::ofe). \<forall>n m. n\<le>m \<longrightarrow> n_equiv n (c m) (c n)}"
  using ofe_eq_limit by force
setup_lifting type_definition_chain
lemmas [simp] = Rep_chain_inverse Rep_chain_inject
lemmas [simp, intro!] = Rep_chain[unfolded mem_Collect_eq]

class cofe = ofe +
  fixes lim :: "('a::ofe) chain \<Rightarrow> 'a"
  assumes core_compl: "n_equiv n (lim c) (Rep_chain c n)"

instantiation unit :: cofe begin
definition lim_unit :: "unit chain \<Rightarrow> unit" where [simp]: "lim_unit _ = ()"
instance by standard (simp add: n_equiv_unit_def)
end

lift_definition option_chain :: "'a::ofe option chain \<Rightarrow> 'a \<Rightarrow> 'a chain" is
  "\<lambda>c x n. case c n of Some y \<Rightarrow> y | None \<Rightarrow> x" 
  by (auto simp: ofe_refl n_equiv_option_def split: option.splits) fastforce+

instantiation option :: (cofe) cofe begin
definition lim_option :: "'a option chain \<Rightarrow> 'a option" where
  "lim_option c \<equiv> case (Rep_chain c 0) of Some x \<Rightarrow> Some (lim (option_chain c x)) | None \<Rightarrow> None"
instance proof
  fix c :: "'a option chain" and n
  have base: "n_equiv 0 (Rep_chain c n) (Rep_chain c 0)" by transfer auto
  from core_compl have step: "n_equiv n (lim (option_chain c x)) (Rep_chain (option_chain c x) n)" for x .
  show "n_equiv n (lim c) (Rep_chain c n)" unfolding lim_option_def
  apply (cases "Rep_chain c 0")
  apply auto
  apply (metis base n_equiv_option_def option.distinct(1))
  by (smt (verit) base step n_equiv_option_def option.simps(5) option_chain.rep_eq)
qed
end

lift_definition later_chain :: "'a::ofe later chain \<Rightarrow> 'a chain" is
  "\<lambda>c n. later_car (Rep_chain c (Suc n))" 
  by transfer (metis Suc_le_mono add_diff_cancel_left' n_equiv_later_def nat.discI plus_1_eq_Suc)

instantiation later :: (cofe) cofe begin
definition lim_later :: "'a later chain \<Rightarrow> 'a later" where
  "lim_later c = Next (lim (later_chain c))"
instance proof
  fix c :: "'a later chain" and n
  from core_compl[of n] show "n_equiv n (lim c) (Rep_chain c n)" 
    apply (auto simp: n_equiv_later_def lim_later_def)
    by (smt (verit, best) One_nat_def Suc_pred' core_compl later_chain.rep_eq not_gr0)
qed
end

definition discrete_lim :: "('a::discrete chain) \<Rightarrow> 'a" where
  "discrete_lim c = Rep_chain c 0"

lemma discrete_cofe: "n_equiv n (discrete_lim c) (Rep_chain c n)"
  unfolding discrete_lim_def by transfer (metis d_equiv nat_le_linear)
end