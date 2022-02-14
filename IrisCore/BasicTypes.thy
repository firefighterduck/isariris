theory BasicTypes
imports Main "HOL-Library.FSet"
begin

subsection \<open>Basic types of camera combinators\<close>

subsubsection \<open>Disjoint set type\<close>
text \<open> Set with extra bottom element to encode non-disjoint unions \<close>
datatype 'a dset = DSet "'a set" | DBot

fun dset_raw :: "'a dset \<Rightarrow> 'a set option" where
  "dset_raw (DSet s) = Some s"
| "dset_raw DBot = None"

fun subdset_eq :: "'a dset \<Rightarrow> 'a dset \<Rightarrow> bool" (infix "\<subseteq>\<^sub>d" 50) where
  "subdset_eq (DSet s) (DSet t) = (s\<subseteq>t)"
| "subdset_eq _ _ = False"

fun dmember :: "'a \<Rightarrow> 'a dset \<Rightarrow> bool" (infix "\<in>\<^sub>d" 50) where
  "dmember x (DSet s) = (x\<in>s)"
| "dmember _ _ = False"

instantiation dset :: (type) minus begin
fun minus_dset :: "'a dset \<Rightarrow> 'a dset \<Rightarrow> 'a dset" where
  "minus_dset (DSet s) (DSet t) = DSet (s-t)"
| "minus_dset (DSet s) DBot = DSet s"
| "minus_dset _ _ = DBot"
instance ..
end

lemma delem_dsubs: "i\<in>\<^sub>d d \<longleftrightarrow> DSet {i} \<subseteq>\<^sub>d d"
  using dmember.elims(2) subdset_eq.elims(2) by fastforce

lemma dsubs_dset: "d1 \<subseteq>\<^sub>d d2 \<Longrightarrow> \<exists>s1 s2. d1 = DSet s1 \<and> d2 = DSet s2"
  using subdset_eq.elims(2) by fastforce

lemma dsubs_raw: "d1 \<subseteq>\<^sub>d d2 \<Longrightarrow> \<exists>s1 s2. dset_raw d1 = Some s1 \<and> dset_raw d2 = Some s2"
  using subdset_eq.elims(2) by fastforce

lemma dminus_raw: "\<lbrakk>dset_raw d1 = Some s1\<rbrakk> \<Longrightarrow> \<exists>s3. dset_raw (d1 - d2) = Some s3"
  by (metis dset.simps(3) dset_raw.elims minus_dset.simps(1) minus_dset.simps(2))

lemma dsubs_minus_inter: "d1 \<subseteq>\<^sub>d d2 \<Longrightarrow> \<exists>s1 s3. Some s3 = (dset_raw (d2 - d1)) \<and> s1 \<inter> s3 = {}"
  using dsubs_raw dminus_raw by (metis inf_bot_left)
  
subsubsection \<open>Disjoint finite set type\<close>
text \<open> Finite set with extra bottom element to encode non-disjoint unions \<close>
datatype 'a dfset = DFSet "'a fset" | DFBot

fun dfmember :: "'a \<Rightarrow> 'a dfset \<Rightarrow> bool" (infix "\<in>\<^sub>f" 50) where
  "dfmember x (DFSet s) = (x|\<in>|s)"
| "dfmember _ _ = False"

fun dset_of_finite :: "'a dfset \<Rightarrow> 'a dset" where
  "dset_of_finite (DFSet f) = DSet (fset f)"
| "dset_of_finite DFBot = DBot"

lemma dset_of_finite_finite: "finite {x. x \<in>\<^sub>d (dset_of_finite f)}"
  by (cases f) auto

subsubsection \<open>Extended sum type\<close>
datatype ('a,'b) sum_ext = Inl 'a | Inr 'b | Inv

type_notation sum_ext (infixl "+\<^sub>e" 15)
lemmas sum_ex2 = sum_ext.exhaust[case_product sum_ext.exhaust]
lemmas sum_ex3 = sum_ext.exhaust[case_product sum_ex2]
lemmas sum_ex4 = sum_ext.exhaust[case_product sum_ex3]

subsubsection \<open>Step indexed predicates\<close>
text \<open>They are defined to hold for all steps below a maximum. \<close>
typedef sprop = "{s::nat\<Rightarrow>bool. \<forall>n m. m\<le>n \<longrightarrow> s n \<longrightarrow> s m}"
proof
  define s :: "nat\<Rightarrow>bool" where "s = (\<lambda>_. True)"
  thus "s \<in> {s::nat\<Rightarrow>bool. \<forall>n m. m\<le>n \<longrightarrow> s n \<longrightarrow> s m}" by simp
qed

setup_lifting type_definition_sprop
lemmas [simp] = Rep_sprop_inverse Rep_sprop_inject
lemmas [simp, intro!] = Rep_sprop[unfolded mem_Collect_eq]

lift_definition sPure :: "bool \<Rightarrow> sprop" is "\<lambda>b _. b" .
lemma sPureId: "Rep_sprop (Abs_sprop ((\<lambda>b _. b) b)) n = b"
  using Abs_sprop_inverse by auto
abbreviation sFalse :: sprop where "sFalse \<equiv> sPure False"
abbreviation sTrue :: sprop where "sTrue \<equiv> sPure True"
lemmas [simp] = sPure.rep_eq sPureId sPureId[simplified sPure.abs_eq[symmetric]]

lift_definition n_subseteq :: "nat \<Rightarrow> sprop \<Rightarrow> sprop \<Rightarrow> bool" is
  "\<lambda>n X Y. \<forall>m\<le>n. X m \<longrightarrow> Y m" .
lift_definition sprop_conj :: "sprop \<Rightarrow> sprop \<Rightarrow> sprop" (infixl "\<and>\<^sub>s" 60) is 
  "\<lambda>x y. (\<lambda>n. x n \<and> y n)" using conj_forward by simp
lift_definition sprop_disj :: "sprop \<Rightarrow> sprop \<Rightarrow> sprop" (infixl "\<or>\<^sub>s" 60) is
  "\<lambda>x y. (\<lambda>n. x n \<or> y n)" using disj_forward by simp
lift_definition sprop_impl :: "sprop \<Rightarrow> sprop \<Rightarrow> sprop" (infixr "\<longrightarrow>\<^sub>s" 60) is
  "\<lambda>x y. (\<lambda>n. \<forall>m\<le>n. x m \<longrightarrow> y m)" by (meson dual_order.trans)

subsubsection \<open>Later camera combinator\<close>
text \<open>This type encodes the later modality on a type level.\<close>
datatype 'a later = Next (later_car: 'a)

lemmas later2_ex = later.exhaust[case_product later.exhaust]
lemmas later3_ex = later.exhaust[case_product later2_ex]

subsubsection \<open>Agreement camera combinator\<close>
typedef 'a ag = "{a::'a set | a. finite a \<and> a\<noteq>{} }"
  by auto

setup_lifting type_definition_ag

lift_definition map_ag :: "('a\<Rightarrow>'b) \<Rightarrow> 'a ag \<Rightarrow> 'b ag" is "(`)" by simp
lift_definition pred_ag :: "('a \<Rightarrow> bool) \<Rightarrow> 'a ag \<Rightarrow> bool" is "\<lambda>P s. Ball s P" .
lift_definition rel_ag :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a ag \<Rightarrow> 'b ag \<Rightarrow> bool" is rel_set .

lift_definition to_ag :: "'a \<Rightarrow> 'a ag" is "\<lambda>a::'a. {a}" by simp

lemma image_ag: "image f (Rep_ag s) \<in> {a |a. finite a \<and> a \<noteq> {}}"
  apply (simp_all add: image_def)
  apply (rule conjI)
  subgoal using finite_imageI[unfolded image_def] Rep_ag by auto
  using Rep_ag by fast
lemmas image_abs_ag = Abs_ag_inverse[OF image_ag] Abs_ag_inject[OF image_ag  image_ag]

context includes cardinal_syntax begin
bnf "'a ag"
  map: map_ag
  sets: Rep_ag
  bd: "natLeq"
  rel: rel_ag
proof -
show "map_ag id = id" by (auto simp: map_ag_def Rep_ag_inverse)
next
fix f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'c"
show "map_ag (g \<circ> f) = map_ag g \<circ> map_ag f" 
  by (auto simp: comp_def image_def map_ag_def)
  (metis Rep_ag_inverse image_def image_image map_ag.rep_eq map_fun_apply)
next
fix x :: "'a ag" and f g :: "'a \<Rightarrow> 'b"
assume "\<And>z. z \<in> Rep_ag x \<Longrightarrow> f z = g z"
then show "map_ag f x = map_ag g x" by transfer auto
next
fix f :: "'a\<Rightarrow>'b"
have "{y. \<exists>x\<in>Rep_ag s. y = f x} = image f (Rep_ag s)" for s by auto
then have "{y. \<exists>x\<in>Rep_ag s. y = f x} \<in> {a |a. finite a \<and> a \<noteq> {}}" for s
  apply simp_all
  apply (rule conjI)
  subgoal using finite_imageI Rep_ag by fast
  using Rep_ag by blast
from Abs_ag_inverse[OF this] show "Rep_ag \<circ> map_ag f = (`) f \<circ> Rep_ag" 
  by (auto simp: map_ag_def image_def comp_def)
next
show "card_order (natLeq )"
  using card_of_card_order_on card_order_csum natLeq_card_order by blast
next
show "cinfinite (natLeq )"
  using cinfinite_csum natLeq_cinfinite by blast
next
fix s :: "'a ag"
show "|Rep_ag s| \<le>o natLeq"
by (metis (no_types, lifting) Rep_ag card_of_Well_order infinite_iff_natLeq_ordLeq mem_Collect_eq 
  natLeq_Well_order not_ordLeq_iff_ordLess ordLess_imp_ordLeq)
next
fix R :: "'a\<Rightarrow>'b\<Rightarrow>bool" and S :: "'b\<Rightarrow>'c\<Rightarrow>bool"
show "rel_ag R OO rel_ag S \<le> rel_ag (R OO S)"
  by (auto simp: rel_ag.rep_eq rel_set_def relcompp.simps) blast+
next
fix R :: "'a\<Rightarrow>'b\<Rightarrow>bool"
show "rel_ag R = (\<lambda>x y. \<exists>z. Rep_ag z \<subseteq> {(x, y). R x y} \<and> map_ag fst z = x \<and> map_ag snd z = y)"
apply (auto simp: rel_ag_def map_ag_def rel_set_def map_fun_def comp_def)
apply standard
apply standard
proof
  fix a :: "'a ag" and b :: "'b ag"
  assume "(\<forall>x\<in>Rep_ag a. \<exists>xa\<in>Rep_ag b. R x xa) \<and> (\<forall>y\<in>Rep_ag b. \<exists>x\<in>Rep_ag a. R x y)"
  then have assms: "\<forall>x\<in>Rep_ag a. \<exists>xa\<in>Rep_ag b. R x xa" "\<forall>y\<in>Rep_ag b. \<exists>x\<in>Rep_ag a. R x y" by simp_all
  define c where c:"c = {(x,y) | x y. x\<in>Rep_ag a \<and> y\<in>Rep_ag b}"
  from Rep_ag have "finite (Rep_ag a)" "Rep_ag a \<noteq> {}" "finite (Rep_ag b)" "Rep_ag b \<noteq> {}" by auto
  with c have c_ag: "finite c" "c \<noteq> {}" by auto
  define c' where c': "c' = c \<inter> {(x,y) | x y. R x y}"
  with c_ag c and assms have c'_ag: "finite c'" "c' \<noteq> {}" by auto
  from c' c assms have c'_alt: "c' = {(x,y) | x y. x\<in>Rep_ag a \<and> y\<in>Rep_ag b \<and> R x y}" by auto
  define z where z: "z = Abs_ag c'"
  then have rep_z: "Rep_ag z = c'" using Abs_ag_inverse c'_ag by auto
  {
    from c'_alt assms(1) have "(fst ` c') = Rep_ag a" by (simp add: image_def) blast
    with rep_z have "Abs_ag (fst ` Rep_ag z) = a" using Rep_ag_inverse by auto
  }
  moreover {
    from c'_alt assms(2) have "(snd ` c') = Rep_ag b" by (simp add: image_def) blast
    with rep_z have "Abs_ag (snd ` Rep_ag z) = b" using Rep_ag_inverse by auto
  }
  moreover have "Rep_ag z \<subseteq> {(x, y). R x y}" using rep_z c' by simp
  ultimately show "\<exists>z. Rep_ag z \<subseteq> {(x, y). R x y} \<and> Abs_ag (fst ` Rep_ag z) = a \<and> Abs_ag (snd ` Rep_ag z) = b"
  by auto
next
  fix a :: "'a ag" and b :: "'b ag"
  assume "\<exists>z. Rep_ag z \<subseteq> {(x, y). R x y} \<and> Abs_ag (fst ` Rep_ag z) = a \<and> Abs_ag (snd ` Rep_ag z) = b"
  then show "(\<forall>x\<in>Rep_ag a. \<exists>xa\<in>Rep_ag b. R x xa) \<and> (\<forall>y\<in>Rep_ag b. \<exists>x\<in>Rep_ag a. R x y)"
  by (smt (verit, best) Product_Type.Collect_case_prodD image_abs_ag(1) image_iff subset_eq)
qed
qed
end

subsubsection \<open>Exclusive camera combinator\<close>
datatype 'a ex = Ex 'a | Inv

subsubsection \<open>Authoritative camera combinator\<close>
datatype 'm auth = Auth "('m ex option\<times>'m)"

abbreviation fragm :: "'m \<Rightarrow> 'm auth" where "fragm \<equiv> \<lambda>a::'m. Auth (None, a)"
abbreviation comb :: "'m \<Rightarrow> 'm \<Rightarrow> 'm auth" where "comb \<equiv> \<lambda>(a::'m) b. Auth (Some (Ex a), b)"
end