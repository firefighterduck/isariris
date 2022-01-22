theory Frac
imports CoreStructures HOL.Rat
begin

subsection \<open> Frac and DFrac \<close>

text \<open> Fractions camera/RA \<close>
text \<open> Positive rational numbers, that are only valid $<= 1$. \<close>
typedef frac = "{p::rat. 0<p}" by (simp add: gt_ex)
setup_lifting type_definition_frac
lemmas [simp] = Rep_frac_inverse Rep_frac_inject
lemmas [simp, intro!] = Rep_frac[unfolded mem_Collect_eq]

instantiation frac :: one begin
lift_definition one_frac :: frac is "1::rat" by simp
instance ..
end
lemmas [simp] = one_frac.rep_eq one_frac_def

instantiation frac :: ofe begin
definition n_equiv_frac :: "nat \<Rightarrow> frac \<Rightarrow> frac \<Rightarrow> bool" where "n_equiv_frac _ \<equiv> (=)"
definition ofe_eq_frac :: "frac \<Rightarrow> frac \<Rightarrow> bool" where "ofe_eq_frac \<equiv> (=)"
instance by standard (auto simp: n_equiv_frac_def ofe_eq_frac_def)
end
instance frac :: discrete by standard (auto simp: n_equiv_frac_def ofe_eq_frac_def)

instantiation frac :: camera begin
lift_definition valid_raw_frac :: "frac \<Rightarrow> sprop" is "\<lambda>p _. (p\<le>1)" .
lift_definition pcore_frac :: "frac \<Rightarrow> frac option" is "\<lambda>_. None" by (rule option.pred_inject(1))
lift_definition op_frac :: "frac \<Rightarrow> frac \<Rightarrow> frac" is "(+)" by simp
instance proof
show "non_expansive (valid_raw::frac \<Rightarrow> sprop)"
  by (rule non_expansiveI) (auto simp: valid_raw_frac_def n_equiv_sprop_def n_equiv_frac_def)
next
show "non_expansive (pcore::frac \<Rightarrow> frac option)" by (rule non_expansiveI) 
  (auto simp: pcore_frac_def n_equiv_option_def n_equiv_frac_def)
next
show "non_expansive2 (op::frac \<Rightarrow> frac \<Rightarrow> frac)" by (rule non_expansive2I) 
  (auto simp: op_frac_def n_equiv_frac_def)
next
fix a b c :: frac
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (auto simp: op_frac_def)
  (metis (mono_tags) Abs_frac_inverse Rep_frac ab_semigroup_add_class.add_ac(1) op_frac.rep_eq)
next
fix a b :: frac
show "a \<cdot> b = b \<cdot> a" by (auto simp: op_frac_def add.commute)
fix a b :: frac
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (auto simp: valid_raw_frac.rep_eq op_frac.rep_eq)
  (metis Rep_frac add_le_same_cancel1 dual_order.trans linorder_not_less mem_Collect_eq nle_le)
qed (auto simp: op_frac_def valid_raw_frac_def n_equiv_frac_def pcore_frac_def)
end

instance frac :: dcamera by (standard; auto simp: valid_raw_frac_def valid_def)

lemma valid_frac: "valid (q::frac) = n_valid q n"
  by (auto simp: valid_def valid_raw_frac_def)
  
instantiation frac :: order begin
lift_definition less_frac :: "frac \<Rightarrow> frac \<Rightarrow> bool" is "(<)" .
lift_definition less_eq_frac :: "frac \<Rightarrow> frac \<Rightarrow> bool" is "(\<le>)" .
instance by standard (auto simp: less_frac.rep_eq less_eq_frac.rep_eq Rep_frac_inject)
end

lemma frac_valid: "valid (p\<cdot>q) \<Longrightarrow> ((p::frac)<1)"
  by (auto simp: valid_def valid_raw_frac.rep_eq less_eq_frac.rep_eq less_frac.rep_eq op_frac.rep_eq)
  (metis Rep_frac less_add_same_cancel1 mem_Collect_eq one_frac.rep_eq one_frac_def order_less_le_trans)

lemma frac_not_valid: "(p::frac)=1 \<Longrightarrow> \<not> valid (p\<cdot>q)"
  by (auto simp: valid_def valid_raw_frac.rep_eq less_eq_frac.rep_eq less_frac.rep_eq op_frac.rep_eq)
  (metis Rep_frac add_le_same_cancel1 linorder_not_less mem_Collect_eq one_frac.rep_eq one_frac_def)

lemma frac_own_incl: "incl (p::frac) q \<longleftrightarrow> (p<q)"
proof (auto simp: incl_def op_frac_def less_frac.rep_eq; transfer; auto simp: Abs_frac_inverse)
  fix p q
  assume assms: "0 < p" "p < Rep_frac q"
  have "(a::rat) < b \<Longrightarrow> \<exists>c. b=a+c" for a b by algebra
  with assms(2) obtain c where rep: "Rep_frac q = p+c" by auto
  then have "q = Abs_frac (p+c)" by (metis Rep_frac_inverse)
  with rep assms(2) show "\<exists>c>0. q = Abs_frac (p + c)" by auto
qed

text \<open> Discardable Fractions Camera \<close>
text \<open> This models fractional ownership which can be given up on.  \<close>

datatype dfrac = DfracOwn frac | DfracDiscarded | DfracBoth frac

lemmas dfrac_ex2 = dfrac.exhaust[case_product dfrac.exhaust]
lemmas dfrac_ex3 = dfrac.exhaust[case_product dfrac_ex2]

instantiation dfrac :: ofe begin
definition n_equiv_dfrac :: "nat \<Rightarrow> dfrac \<Rightarrow> dfrac \<Rightarrow> bool" where [simp]: "n_equiv_dfrac _ \<equiv> (=)"
definition ofe_eq_dfrac :: "dfrac \<Rightarrow> dfrac \<Rightarrow> bool" where [simp]: "ofe_eq_dfrac \<equiv> (=)"
instance by standard auto
end
instance dfrac :: discrete by standard auto

fun dfrac_add :: "dfrac \<Rightarrow> dfrac \<Rightarrow> dfrac" where
  "dfrac_add (DfracOwn q) (DfracOwn q') = DfracOwn (q \<cdot> q')"
| "dfrac_add (DfracOwn q) DfracDiscarded = DfracBoth q"
| "dfrac_add (DfracOwn q) (DfracBoth q') = DfracBoth (q \<cdot> q')"
| "dfrac_add DfracDiscarded (DfracOwn q') = DfracBoth q'"
| "dfrac_add DfracDiscarded DfracDiscarded = DfracDiscarded"
| "dfrac_add DfracDiscarded (DfracBoth q') = DfracBoth q'"
| "dfrac_add (DfracBoth q) (DfracOwn q') = DfracBoth (q \<cdot> q')"
| "dfrac_add (DfracBoth q) DfracDiscarded = DfracBoth q"
| "dfrac_add (DfracBoth q) (DfracBoth q') = DfracBoth (q \<cdot> q')"

instantiation dfrac :: camera begin
lift_definition valid_raw_dfrac :: "dfrac \<Rightarrow> sprop" is 
  "\<lambda>dq. case dq of DfracOwn q \<Rightarrow> valid_raw q | DfracDiscarded \<Rightarrow> sTrue | DfracBoth q \<Rightarrow> sPure (q<1)" .
definition pcore_dfrac :: "dfrac \<Rightarrow> dfrac option" where "pcore_dfrac dq \<equiv>
  case dq of DfracOwn _ \<Rightarrow> None | _ \<Rightarrow> Some DfracDiscarded"
definition op_dfrac :: "dfrac \<Rightarrow> dfrac \<Rightarrow> dfrac" where "op_dfrac \<equiv> dfrac_add"
instance proof
show "non_expansive (valid_raw::dfrac \<Rightarrow> sprop)" 
  by (rule non_expansiveI) (auto simp: valid_raw_dfrac_def ofe_refl split: dfrac.splits)
next
show "non_expansive (pcore::dfrac \<Rightarrow> dfrac option)"
  by (rule non_expansiveI) (auto simp: pcore_dfrac_def n_equiv_option_def split: dfrac.splits)
next
show "non_expansive2 (op::dfrac \<Rightarrow> dfrac \<Rightarrow> dfrac)"
  by (rule non_expansive2I) (auto simp: op_dfrac_def)
next
fix a b c :: dfrac
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (cases a b c rule: dfrac_ex3) (auto simp: op_dfrac_def camera_assoc)
next
fix a b :: dfrac
show "a \<cdot> b = b \<cdot> a" by (cases a; cases b) (auto simp: op_dfrac_def camera_comm)
next
fix a a' :: dfrac
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" by (cases a; cases a') (auto simp: pcore_dfrac_def op_dfrac_def)
next
fix a a' :: dfrac
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" by (cases a; cases a') (auto simp: pcore_dfrac_def)
next
fix a a' b :: dfrac
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  by (cases a a' b rule: dfrac_ex3; auto simp: pcore_dfrac_def op_dfrac_def)
  (metis dfrac.exhaust dfrac.simps(6) dfrac_add.simps(4-9) dfrac.distinct(3))+
next
fix a b :: dfrac
fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (cases a; cases b;auto simp: valid_raw_dfrac_def op_dfrac_def camera_valid_op Abs_frac_inverse less_frac.rep_eq valid_raw_frac.rep_eq)
  (metis Rep_frac add_le_same_cancel1 dual_order.strict_trans linorder_not_le mem_Collect_eq op_frac.rep_eq camera_valid_op less_eq_rat_def valid_raw_frac.rep_eq)+
next
fix a b1 b2 :: dfrac
fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b1 \<cdot> b2) \<Longrightarrow> \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b1 \<and> n_equiv n c2 b2"
  by (cases a; cases b1; cases b2) (auto simp: valid_raw_dfrac_def op_dfrac_def)
qed
end

instance dfrac :: dcamera 
  apply (standard; auto simp: valid_raw_dfrac_def valid_def  split: dfrac.splits)
  using d_valid[simplified valid_def] by fast

lemma dfrac_own_incl: "incl (DfracOwn p) (DfracOwn q) \<longleftrightarrow> (p<q)"
proof (standard; unfold incl_def op_dfrac_def)
  assume "\<exists>c. DfracOwn q = dfrac_add (DfracOwn p) c"
  then obtain c where "DfracOwn q = dfrac_add (DfracOwn p) (DfracOwn c)"
    by (metis camera_assoc camera_comm dfrac.distinct(3) dfrac.exhaust dfrac_add.simps(4) dfrac_add.simps(6) op_dfrac_def)
  then have "q = p\<cdot>c" by simp
  then have "incl p q" by (auto simp: incl_def)
  then show "p<q" by (simp add: frac_own_incl)
next
  assume "p<q"
  then obtain c where "q=p\<cdot>c" using incl_def frac_own_incl by metis
  then have "DfracOwn q = dfrac_add (DfracOwn p) (DfracOwn c)" by simp
  then show "\<exists>c. DfracOwn q = dfrac_add (DfracOwn p) c" by fast
qed

lemma valid_dfrac: "valid (q::dfrac) = n_valid q n"
  apply (simp add: valid_def valid_raw_dfrac_def split: dfrac.splits) 
  using valid_frac by auto

lemma dfrac_valid_own_r: "valid (dq \<cdot> DfracOwn q) \<Longrightarrow> (q < 1)"
apply (cases dq) apply (simp_all add: op_dfrac_def valid_raw_dfrac_def valid_def split: dfrac.splits)
apply (metis camera_comm frac_valid one_frac_def valid_frac)
unfolding op_frac_def
by (metis Rep_frac dual_order.strict_trans less_add_same_cancel2 less_frac.rep_eq mem_Collect_eq op_frac.rep_eq op_frac_def)

lemma dfrac_valid_own_l: "valid (DfracOwn q \<cdot> dq) \<Longrightarrow> (q < 1)"
  using dfrac_valid_own_r camera_comm by metis

lemma dfrac_not_valid_own: "\<not> valid (DfracOwn 1 \<cdot> dq)"
apply (cases dq) apply (simp_all add: valid_def valid_raw_dfrac.rep_eq op_dfrac_def split: dfrac.splits)
apply (metis frac_not_valid one_frac_def valid_frac)
by (meson dual_order.asym frac_own_incl incl_def)
  
lemma dfrac_discard_update: "dq \<leadsto> {DfracDiscarded}"
proof (auto simp: fup_def)
fix x
assume assms: "valid dq" "valid (dq \<cdot> x)"
show "valid (DfracDiscarded \<cdot> x)"
proof (cases x)
  case (DfracOwn x1)
  with assms(2) have "x1<Abs_frac 1" using dfrac_valid_own_r by simp
  with DfracOwn show ?thesis by (auto simp: op_dfrac_def valid_def valid_raw_dfrac.rep_eq)
next
  case DfracDiscarded
  then show ?thesis by (auto simp: op_dfrac_def valid_raw_dfrac.rep_eq valid_def)
next
  case (DfracBoth x3)
  from assms(2) have "valid x" unfolding valid_def using camera_comm camera_valid_op by metis
  with DfracBoth show ?thesis by (auto simp: valid_def op_dfrac_def valid_raw_dfrac.rep_eq)
qed
qed
end