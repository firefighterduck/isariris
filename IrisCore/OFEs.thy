theory OFEs
imports BasicTypes
begin

section \<open> Ordered family of equivalences \<close>
text \<open> The definition of the class of OFEs and some instances. \<close>

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

subsection \<open> Basic OFE instances \<close>
subsubsection \<open>unit OFE\<close>
instantiation unit :: ofe begin
  definition n_equiv_unit :: "nat \<Rightarrow> unit \<Rightarrow> unit \<Rightarrow> bool" where
    "n_equiv_unit _ _ _ = True"
  fun ofe_eq_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" where "ofe_eq_unit _ _ = True"
instance by (standard, unfold n_equiv_unit_def) auto
end

instance unit :: discrete by standard (auto simp: n_equiv_unit_def)

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

subsubsection \<open>Set type OFE\<close>
instantiation set :: (type) ofe begin
definition n_equiv_set :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "n_equiv_set _ \<equiv> (=)"
definition ofe_eq_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "ofe_eq_set \<equiv> (=)"
instance by (standard) (auto simp: n_equiv_set_def ofe_eq_set_def)
end

instance set :: (type) discrete by standard (auto simp: n_equiv_set_def ofe_eq_set_def)

subsubsection \<open>Disjoint set OFE\<close>
instantiation dset :: (type) ofe begin
definition n_equiv_dset :: "nat \<Rightarrow> 'a dset \<Rightarrow> 'a dset \<Rightarrow> bool" where "n_equiv_dset \<equiv> \<lambda>_. (=)"
definition ofe_eq_dset :: "'a dset \<Rightarrow> 'a dset \<Rightarrow> bool" where "ofe_eq_dset \<equiv> (=)"
instance by standard (auto simp: n_equiv_dset_def ofe_eq_dset_def)
end

instance dset :: (type) discrete by standard (auto simp: n_equiv_dset_def ofe_eq_dset_def)

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

subsubsection \<open>Function type OFE\<close>
instantiation "fun" :: (type,ofe) ofe begin
definition n_equiv_fun :: "nat \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool" where
  "n_equiv_fun n m1 m2 \<equiv> \<forall>i. n_equiv n (m1 i) (m2 i)"
definition ofe_eq_fun :: "('a\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool" where
  "ofe_eq_fun m1 m2 \<equiv> \<forall>i. ofe_eq (m1 i) (m2 i)"
instance by (standard, unfold n_equiv_fun_def ofe_eq_fun_def) 
  (auto simp: ofe_sym  ofe_limit intro: ofe_refl ofe_trans ofe_mono ofe_limit ofe_eq_eq)
end

instance "fun" :: (type,discrete) discrete 
  by standard (auto simp: n_equiv_fun_def d_equiv ofe_eq_fun_def d_eq)

subsubsection \<open>Finite set OFE\<close>
instantiation fset :: (type) ofe begin
definition n_equiv_fset :: "nat \<Rightarrow> 'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where [simp]: "n_equiv_fset _ \<equiv> (=)"
definition ofe_eq_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where [simp]: "ofe_eq_fset \<equiv> (=)"
instance by (standard) auto
end

instance fset :: (type) discrete by standard auto

subsubsection \<open>Disjoint finite set OFE\<close>
instantiation dfset :: (type) ofe begin
definition n_equiv_dfset :: "nat \<Rightarrow> 'a dfset \<Rightarrow> 'a dfset \<Rightarrow> bool" where "n_equiv_dfset \<equiv> \<lambda>_. (=)"
definition ofe_eq_dfset :: "'a dfset \<Rightarrow> 'a dfset \<Rightarrow> bool" where "ofe_eq_dfset \<equiv> (=)"
instance by standard (auto simp: n_equiv_dfset_def ofe_eq_dfset_def)
end

instance dfset :: (type) discrete by standard (auto simp: n_equiv_dfset_def ofe_eq_dfset_def)

subsubsection \<open>Extended sum type\<close>
instantiation sum_ext :: (ofe,ofe) ofe begin
  fun ofe_eq_sum_ext :: "'a+\<^sub>e'b \<Rightarrow> 'a+\<^sub>e'b \<Rightarrow> bool" where
    "ofe_eq_sum_ext (Inl a) (Inl b) = ofe_eq a b"
  | "ofe_eq_sum_ext (Inr a) (Inr b) = ofe_eq a b"
  | "ofe_eq_sum_ext sum_ext.Inv sum_ext.Inv = True"
  | "ofe_eq_sum_ext _ _ = False"
  fun n_equiv_sum_ext :: "nat \<Rightarrow> 'a+\<^sub>e'b \<Rightarrow> 'a+\<^sub>e'b \<Rightarrow> bool" where
    "n_equiv_sum_ext n (Inl x) (Inl y) = n_equiv n x y"
  | "n_equiv_sum_ext n (Inr x) (Inr y) =  n_equiv n x y"
  | "n_equiv_sum_ext _ sum_ext.Inv sum_ext.Inv = True"
  | "n_equiv_sum_ext _ _ _ = False"
instance proof
  fix n x
  show "n_equiv n x (x::'a+\<^sub>e'b)" by (cases x) (auto simp: ofe_refl)
next
  fix n x y
  show "n_equiv n x y = n_equiv n y (x::'a+\<^sub>e'b)" 
    by (cases x y rule: sum_ex2) (auto simp: ofe_sym)
next
  fix n x y z 
  show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x (z::'a+\<^sub>e'b)"
    by (cases x y z rule: sum_ex3) (auto intro: ofe_trans)
next
  fix m n x y
  show "m \<le> n \<Longrightarrow> n_equiv n x y \<Longrightarrow> n_equiv m x (y::'a+\<^sub>e'b)"
  by (cases x y rule: sum_ex2) (auto intro: ofe_mono)
next
  fix x y :: "'a+\<^sub>e'b"
  show "ofe_eq x y \<longleftrightarrow> (\<forall>n. n_equiv n x y)"
  apply (cases x; cases y) 
  apply simp_all
  using ofe_limit by blast+
next
  fix x y :: "'a+\<^sub>e'b" 
  show "(x=y) \<Longrightarrow> ofe_eq x y" by (cases x y rule: sum_ex2) (auto intro: ofe_eq_eq)
qed
end

instance sum_ext :: (discrete,discrete) discrete
proof
fix a b :: "'a+\<^sub>e'b" fix n
show "n_equiv n a b = (a = b)" by (cases a b rule: sum_ex2) (auto simp: d_equiv)
next
fix a b :: "'a+\<^sub>e'b"
show "ofe_eq a b = (a = b)" by (cases a b rule: sum_ex2) (auto simp: d_eq)
qed

subsection \<open> Advanced OFE instances\<close>

subsubsection \<open> Step indexed proposition OFE\<close> 
instantiation sprop :: ofe begin
  definition n_equiv_sprop :: "nat \<Rightarrow> sprop \<Rightarrow> sprop \<Rightarrow> bool" where
    "n_equiv_sprop n x y \<equiv> \<forall>m\<le>n. Rep_sprop x m \<longleftrightarrow> Rep_sprop y m"
  definition ofe_eq_sprop :: "sprop \<Rightarrow> sprop \<Rightarrow> bool" where
    "ofe_eq_sprop x y \<equiv> \<forall>n. (Rep_sprop x n) \<longleftrightarrow> (Rep_sprop y n)"
instance by (standard, unfold n_equiv_sprop_def ofe_eq_sprop_def) auto
end

subsubsection \<open>later type OFE\<close>
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
    by (cases n; cases x y rule: later2_ex) (auto simp: ofe_limit ofe_sym n_equiv_later_def)
next
  fix x y n z
  show "n_equiv n (x::'a later) y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x z"
    by (cases n; cases x y z rule: later3_ex) (auto simp: n_equiv_later_def intro: ofe_trans)
next
  fix m n x y
  show "m \<le> n \<Longrightarrow> (n_equiv::nat\<Rightarrow>'a later\<Rightarrow>'a later\<Rightarrow>bool) n x y \<Longrightarrow> n_equiv m x y"
    by (cases m; cases n; cases x y rule: later2_ex) (auto simp: ofe_mono n_equiv_later_def)
next
  fix x y :: "'a later"
  show "(ofe_eq x y) \<longleftrightarrow> (\<forall>n. n_equiv n x y)"
  by (cases x y rule: later2_ex)
    (metis Zero_not_Suc diff_Suc_1 later.sel n_equiv_later_def ofe_eq_later.simps ofe_limit)
next
fix x y :: "'a later"
show "(x=y) \<Longrightarrow> ofe_eq x y" using OFEs.ofe_eq_later.elims(3) ofe_eq_eq by auto
qed
end

subsubsection \<open>Agreement camera combinator OFE\<close>
instantiation ag :: (ofe) ofe begin
lift_definition n_equiv_ag :: "nat \<Rightarrow> ('a::ofe) ag \<Rightarrow> 'a ag \<Rightarrow> bool" is
  "\<lambda>n a b. (\<forall>x\<in>a. \<exists>y\<in>b. n_equiv n x y) \<and> (\<forall>y\<in>b. \<exists>x\<in>a. n_equiv n x y)" .
definition ofe_eq_ag :: "('a::ofe) ag \<Rightarrow> 'a ag \<Rightarrow> bool" where
  "ofe_eq_ag a b \<equiv> \<forall>n. n_equiv n a b"
lemmas defs = n_equiv_ag.rep_eq ofe_eq_ag_def
instance by (standard) (auto 4 4 simp: defs ofe_sym intro: ofe_refl ofe_trans ofe_mono)
end

instance ag :: (discrete) discrete apply standard
  apply (simp_all add: n_equiv_ag.rep_eq d_equiv ofe_eq_ag_def)
  using Rep_ag_inject by blast+

subsubsection \<open>Exclusive camera combinator OFE\<close>
instantiation ex :: (ofe) ofe begin
fun n_equiv_ex :: "nat \<Rightarrow> 'a::ofe ex \<Rightarrow> 'a ex \<Rightarrow> bool" where
  "n_equiv_ex n (Ex a) (Ex b) = n_equiv n a b"
| "n_equiv_ex _ ex.Inv ex.Inv = True"
| "n_equiv_ex _ _ _ = False"
fun ofe_eq_ex :: "'a ex \<Rightarrow> 'a ex \<Rightarrow> bool" where
  "ofe_eq_ex (Ex a) (Ex b) = ofe_eq a b"
| "ofe_eq_ex ex.Inv ex.Inv = True"
| "ofe_eq_ex _ _ = False"
instance proof
fix x n show "n_equiv n x (x::'a ex)" by (cases x) (auto intro: ofe_refl)
next fix n x y show "n_equiv n x y = n_equiv n y (x::'a ex)" by (cases x; cases y) (auto simp: ofe_sym)
next fix n x y z show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x (z::'a ex)"
  by (cases x; cases y; cases z) (auto intro: ofe_trans)
next fix m n x y show "m \<le> n \<Longrightarrow> n_equiv n x y \<Longrightarrow> n_equiv m x (y::'a ex)" 
  by (cases x; cases y) (auto intro: ofe_mono)
next fix x y show "ofe_eq x y \<longleftrightarrow> (\<forall>n. n_equiv n x (y::'a ex))" 
  apply (cases x; cases y) apply simp_all using ofe_limit by blast+
next fix x y show "x = y \<Longrightarrow> ofe_eq x (y::'a ex)" by (cases x; cases y) (auto intro: ofe_eq_eq)
qed
end

instance ex :: (discrete) discrete
proof
fix a b :: "'a ex" fix n
show "n_equiv n a b = (a = b)" by (cases a; cases b) (auto simp: d_equiv)
next
fix a b :: "'a ex"
show "ofe_eq a b = (a = b)" by (cases a; cases b) (auto simp: d_eq)
qed

subsubsection \<open>Authoritative camera combinator OFE\<close>

instantiation auth :: (ofe) ofe begin
fun n_equiv_auth :: "nat \<Rightarrow> 'a auth \<Rightarrow> 'a auth \<Rightarrow> bool" where
  "n_equiv_auth n (Auth a) (Auth b) = n_equiv n a b"
fun ofe_eq_auth :: "'a auth \<Rightarrow> 'a auth \<Rightarrow> bool" where
  "ofe_eq_auth (Auth a) (Auth b) = ofe_eq a b"
instance proof
fix n x show "n_equiv n x (x::'a auth)" by (cases x) (auto intro: ofe_refl) next
fix n x y show "n_equiv n x y \<longleftrightarrow> n_equiv n y (x::'a auth)" 
  by (cases x; cases y) (auto simp: ofe_sym) next
fix n x y z show "n_equiv n x y \<Longrightarrow> n_equiv n y z \<Longrightarrow> n_equiv n x (z::'a auth)"
  by (cases x; cases y; cases z) (auto intro: ofe_trans) next 
fix m n x y show "m \<le> n \<Longrightarrow> n_equiv n x y \<Longrightarrow> n_equiv m x (y::'a auth)"
  by (cases x; cases y) (auto intro: ofe_mono) next
fix x y show "ofe_eq x y \<longleftrightarrow> (\<forall>n. n_equiv n x (y::'a auth))" apply (cases x; cases y; auto)
  using ofe_limit by blast+ next
fix x y show " x = y \<Longrightarrow> ofe_eq x (y::'a auth)" by (cases x; cases y) (auto intro: ofe_eq_eq)
qed
end

instance auth :: (discrete) discrete
proof
fix a b :: "'a auth" fix n
show "n_equiv n a b = (a = b)" by (cases a; cases b) (auto simp: d_equiv)
next
fix a b :: "'a auth"
show "ofe_eq a b = (a = b)" by (cases a; cases b) (auto simp: d_eq)
qed


end