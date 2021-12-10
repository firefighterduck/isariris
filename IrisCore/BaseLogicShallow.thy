theory BaseLogicShallow
imports CoreStructures
begin

subsection \<open> Uniform Predicates \<close>
text \<open> A first try to formalize uniform predicates based on monotone, non-expansive fucntions. \<close>
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

abbreviation rep_mon :: "'a mon_ne \<Rightarrow> 'a::camera \<Rightarrow> sprop" where 
  "rep_mon \<equiv> Rep_non_expansive \<circ> Rep_mon_ne"

abbreviation abs_mon :: "('a::camera \<Rightarrow> sprop) \<Rightarrow> 'a mon_ne" where
  "abs_mon \<equiv> Abs_mon_ne \<circ> Abs_non_expansive"  
  
definition mon_ne_equiv :: "('a::camera) mon_ne \<Rightarrow> 'a mon_ne \<Rightarrow> bool" where
  "mon_ne_equiv x y = (\<forall>m a. Rep_sprop (rep_valid_raw a) m 
    \<longrightarrow> (Rep_sprop (rep_mon x a) m \<longleftrightarrow> Rep_sprop (rep_mon y a) m))"

(* Then the actual uniform predicate *)
quotient_type (overloaded) 'b upred = "('b::camera) mon_ne" / mon_ne_equiv
  by (simp add: mon_ne_equiv_def equivp_reflp_symp_transp reflp_def symp_def transp_def)

instantiation upred :: (camera) cofe begin
  lift_definition lim_uprop :: "(nat \<Rightarrow> 'a upred) \<Rightarrow> 'a upred" is
    "\<lambda>c. abs_mon (\<lambda>x. Abs_sprop (\<lambda>n. \<forall>n'\<le>n. Rep_sprop (rep_valid_raw x) n' 
      \<longrightarrow> Rep_sprop (rep_mon (c n') x) n ))"
  sorry (* This is a direct translation from the Coq formalization, so it should hold. *)
    
  lift_definition n_equiv_uprop :: "nat \<Rightarrow> 'a upred \<Rightarrow> 'a upred \<Rightarrow> bool" is
    "\<lambda>n x y. \<forall>m\<le>n. \<forall>a. Rep_sprop (rep_valid_raw a) m \<longrightarrow> (Rep_sprop (rep_mon x a) m \<longleftrightarrow> Rep_sprop (rep_mon y a) m)"
    by (auto simp: mon_ne_equiv_def)

  lift_definition ofe_eq_uprop :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> bool" is "\<lambda>x y. mon_ne_equiv x y" 
    unfolding mon_ne_equiv_def by auto
instance sorry
end

text \<open> A better upred formalization as a semantic subtype of functions, shallow embedding \<close>
typedef (overloaded) 'm upred_f = "{f::('m::total_camera \<Rightarrow> nat \<Rightarrow> bool). 
  \<forall>n m x y. f x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> f y m}"
  proof
  define uTrue where "uTrue \<equiv> \<lambda>x::'m. \<lambda>n::nat. True"
  hence "\<forall>n m x y. uTrue x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> uTrue y m" by fast
  thus "uTrue \<in> {f. \<forall>n m x y. f x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> f y m}" by blast
qed

setup_lifting type_definition_upred_f
lemmas [simp] = Rep_upred_f_inverse Rep_upred_f_inject
lemmas [simp, intro!] = Rep_upred_f[unfolded mem_Collect_eq]

instantiation upred_f :: (total_camera) ofe begin
  lift_definition n_equiv_upred_f :: "nat \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" is
    "\<lambda>n P Q. \<forall>a m. m\<le>n \<longrightarrow> valid_n a m \<longrightarrow> (P a m \<longleftrightarrow> Q a m)" .
  lift_definition ofe_eq_upred_f :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" is 
    "\<lambda>P Q. \<forall>a n. valid_n a n \<longrightarrow> (P a n \<longleftrightarrow> Q a n)" .
instance by (standard) (auto simp: n_equiv_upred_f.rep_eq ofe_eq_upred_f.rep_eq)
end    
instantiation upred_f :: (total_camera) cofe begin
  lift_definition lim_upred_f :: "(nat \<Rightarrow> 'a upred_f) \<Rightarrow> 'a upred_f" is
    "\<lambda>c a n. \<forall>m\<le>n. valid_n a m \<longrightarrow> c m a m" 
    by (meson camera_valid_op eq_imp_le ne_sprop_weaken ofe_mono order.trans n_incl_def)
instance by (standard; auto simp: is_chain_def; transfer; auto)
  (meson ne_sprop_weaken ofe_refl order_refl total_n_inclI)
end

text \<open> upred as a predicate on functions\<close>
definition upred_def :: "('m::total_camera \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where 
  [simp]: "upred_def P = (\<forall>n m x y. P x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> P y m)"
lemma upred_defI[intro?]: 
  assumes "\<And>n m x y. \<lbrakk>P x n; n_incl m x y; m\<le>n\<rbrakk> \<Longrightarrow> P y m"
  shows "upred_def P"
  using assms by auto

lemma upred_def_rep: "upred_def (Rep_upred_f f)" using Rep_upred_f upred_def_def by blast

lemma upred_weaken: "\<lbrakk>n_equiv n x y; m\<le>n;upred_def f; f x n\<rbrakk> \<Longrightarrow> f y m"
  using Rep_upred_f total_n_inclI upred_def_def by fast

lemma upred_weaken_simple: "\<lbrakk>upred_def f; f x n; m\<le>n\<rbrakk> \<Longrightarrow> f x m"
  using ofe_refl upred_weaken by blast 

(* Arcane Isabelle magic, presented to you by Manuel Eberl *)
context assumes "SORT_CONSTRAINT('a::total_camera)"
begin

(* This shows that upred and upred_f are equivalent types. *)
theorem upred_equiv_upred_f: 
  "(\<forall>n1 n2 x1 (x2::'a). f x1 n1 \<longrightarrow> n_incl n1 x1 x2 \<longrightarrow> n2\<le>n1 \<longrightarrow> f x2 n2) \<longleftrightarrow> 
  ((\<forall>x n m. m \<le> n \<longrightarrow> f x n \<longrightarrow> f x m) \<and>
  (\<forall>n x y. n_equiv n x y\<longrightarrow>(\<forall>m\<le>n. f x m \<longleftrightarrow> f y m)) \<and>
  (\<forall>n x y. n_incl n x y \<longrightarrow> (\<forall>m\<le>n. f x m \<longrightarrow> f y m)))" 
(is "?u f \<longleftrightarrow> (?sprop f \<and> ?ne f \<and> ?mon f)")
proof
assume assm: "?u f"
then show "?sprop f \<and> ?ne f \<and> ?mon f" apply auto
  using total_n_inclI ofe_refl apply blast
  using total_n_inclI apply blast
  apply (meson total_n_inclI ofe_sym order_refl)
  by (meson camera_n_incl_le order_refl total_n_inclI)
next
assume assm: "?sprop f \<and> ?ne f \<and> ?mon f"
show "?u f" by (simp add: assm)
qed

text \<open> The semantic of uniform predicates is defined as a shallow embedding. \<close>

lift_definition uPure :: "bool \<Rightarrow> 'a upred_f" ("\<upharpoonleft>_") is "\<lambda>b. \<lambda>_::'a. \<lambda>_::nat. b" .

lift_definition upred_eq :: "'b::ofe \<Rightarrow> 'b \<Rightarrow> 'a::total_camera upred_f" (infix "=\<^sub>u" 60) is 
  "\<lambda>x (y::'b). \<lambda>_::'a. \<lambda>n. ofe_class.n_equiv n x y" by (rule ofe_mono)

lift_definition upred_conj :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<and>\<^sub>u" 60) is
  "\<lambda>x y a n. x a n \<and> y a n" by (rule conj_forward)
lift_definition upred_disj :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<or>\<^sub>u" 60) is
  "\<lambda>x y a n. x a n \<or> y a n" by (rule disj_forward)

lift_definition upred_impl :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixr "\<longrightarrow>\<^sub>u" 60) is
  "\<lambda>x y (a::'a) n. (\<forall>m\<le>n. \<forall>b. incl a b \<longrightarrow> valid_n b m \<longrightarrow> x b m \<longrightarrow> y b m)"
proof -
  fix x y n n' a b m c
  assume assms: "n_incl n' a (b::'a)" "n'\<le>n" "m\<le>n'" "incl b c" "valid_n c m" "x c m" 
  assume x_upred: "(\<And>n m x' y. x x' n \<Longrightarrow> n_incl m x' y \<Longrightarrow> m \<le> n \<Longrightarrow> x y m)"
  assume y_upred: "(\<And>n m x (y'::'a). y x n \<Longrightarrow> n_incl m x y' \<Longrightarrow> m \<le> n \<Longrightarrow> y y' m)"
  assume I: "(\<And>m b. m \<le> n \<Longrightarrow> incl a b \<Longrightarrow> valid_n b m \<Longrightarrow> x b m \<Longrightarrow> y b m)"
  from \<open>n_incl n' a b\<close> obtain b' where b': "n_equiv n' b (rep_comp (a,b'))" using n_incl_def by blast
  from \<open>incl b c\<close> obtain c' where c':"c = rep_comp (b,c')" using incl_def by blast
  with assms have "valid_n (rep_comp (b,c')) m" by simp
  with b' have vabc: "valid_n (rep_comp (rep_comp (a,b'),c')) m" 
    by (meson assms(3) valid_comp_comp_weaken ofe_mono)
  from c' \<open>x c m\<close> have xbc':"x (rep_comp (b,c')) m"  by simp
  have bc_abc: "n_equiv m (rep_comp (b,c')) (rep_comp (rep_comp (a,b'),c'))" 
    using ofe_class.ofe_mono[OF assms(3) comp_equiv[OF b', of c' c', simplified ofe_class.ofe_refl, simplified]] .
  from upred_weaken[OF this, of m, simplified] x_upred xbc'
  have xabc: "x (rep_comp (rep_comp (a,b'),c')) m" by metis
  from bc_abc c' have "n_equiv m (rep_comp (rep_comp (a,b'),c')) c" by (simp add:ofe_class.ofe_sym)
  from upred_weaken[OF this, of m, simplified, of y] have yabc: "y (rep_comp (rep_comp (a,b'),c')) m \<Longrightarrow> y c m" 
    using y_upred by blast
  have "incl a (rep_comp (rep_comp (a, b'), c'))" using incl_comp_extend incl_def by blast  
  from yabc[OF I[OF order.trans[OF assms(3,2)] this vabc xabc]]
  show "y c m".
qed

lift_definition upred_forall :: "('b \<Rightarrow> 'a upred_f) \<Rightarrow> 'a upred_f" ("\<forall>\<^sub>u _") is "\<lambda>f a n. \<forall>x. f x a n" 
  by (rule meta_allE)

lift_definition upred_exists :: "('b \<Rightarrow> 'a upred_f) \<Rightarrow> 'a upred_f" ("\<exists>\<^sub>u _") is "\<lambda>f a n. \<exists>x. f x a n"
  by (rule ex_forward)

lift_definition upred_sep :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<^emph>" 60) is
  "\<lambda>x y a n. \<exists>b1 b2. n_equiv n a (rep_comp (b1,b2)) \<and> x b1 n \<and> y b2 n"
proof auto
  fix P Q n m a b c1 c2
  assume assms: "n_incl m a (b::'a)" "m\<le>n"
  assume I: "n_equiv n a (rep_comp (c1, c2))" "P c1 n" "Q c2 n"
  assume Q: "(\<And>n m x y. Q x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> Q y m)"
  assume "(\<And>n m x y. P x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> P y m)"
  then have P: "upred_def P" by auto
  from assms obtain c where c:"n_equiv m b (rep_comp (a,c))" using n_incl_def by blast
  from comp_equiv_subst[OF this I(1) assms(2)] have "n_equiv m b (rep_comp (rep_comp (c1,c2),c))" .
  then have bc: "n_equiv m b (rep_comp (c1, rep_comp (c2,c)))" 
    by (metis camera_class.camera_assoc)
  from upred_weaken_simple[OF P I(2) assms(2)] have c1: "P c1 m" .
  from Q[OF I(3), of m, OF n_incl_comp_extend assms(2), of c] have "Q (rep_comp (c2,c)) m" .
  with bc c1 show "\<exists>b1 b2. n_equiv m b (rep_comp (b1, b2)) \<and> P b1 m \<and> Q b2 m" by blast
qed

lift_definition upred_wand :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixr "-\<^emph>" 60) is 
  "\<lambda>P Q a n. \<forall>b m. m\<le>n \<longrightarrow> valid_n (rep_comp (a,b)) m \<longrightarrow> P b m \<longrightarrow> Q (rep_comp (a,b)) m"
proof -
  fix P Q n n' a b c m
  assume Q: "\<And>n m x y. Q (x::'a) n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> Q y m"
  assume I: "(\<And>b m. m\<le>n \<Longrightarrow> valid_n (rep_comp (a, b)) m \<Longrightarrow> P b m \<Longrightarrow> Q (rep_comp (a, b)) m)"
  assume assms: "n_incl n' a (b::'a)" "n'\<le>n" "m\<le>n'" " valid_n (rep_comp (b, c)) m" "P c m"
  from assms have "m\<le>n" by linarith
  from Q[OF I[OF this valid_n_incl_subst[OF assms(1,4,3)] assms(5)] n_incl_extend[OF assms(1,3)] order.refl]
  show "Q (rep_comp (b,c)) m" .
qed

lift_definition upred_own :: "'a \<Rightarrow> 'a upred_f" ("Own(_)") is "\<lambda>a b n. n_incl n a b" 
  by (metis (full_types) camera_assoc comp_equiv_subst n_incl_def)

lift_definition upred_valid :: "'a \<Rightarrow> 'a upred_f" ("\<V>(_)") is "\<lambda>a _. valid_n a" 
  using Rep_sprop n_incl_def by blast
  
lift_definition upred_persis :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<box>_") is "\<lambda>P a. P (total_core a)"
apply (auto simp: total_core_def n_incl_def split: option.splits)
apply (metis \<epsilon>_left_id ofe_refl)
apply (metis \<epsilon>_left_id ofe_eq_limit)
apply (metis \<epsilon>_core \<epsilon>_left_id camera_core_mono option.distinct(1))
proof -
fix f n m a b x c y
assume "m\<le>n" "(\<And>n m x y. f x n \<Longrightarrow> \<exists>c. n_equiv m y (rep_comp (x, c)) \<Longrightarrow> m \<le> n \<Longrightarrow> f y m)"
  "rep_core (a::'a) = Some x" "n_equiv m b (rep_comp (a, c))" "f x n" "rep_core b = Some y"
from camera_core_mono[of a b] have "n_equiv m y (rep_comp (x,c))" sorry
show "f y m" sorry
qed

lift_definition upred_plain :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<^item>_") is "\<lambda>P _ n. P \<epsilon> n"
  by (metis \<epsilon>_left_id ofe_eq_limit n_incl_def)

lift_definition upred_later :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<triangleright>_") is "\<lambda>P a n. n=0 \<or> P a (n-1)" 
  by (smt (verit, ccfv_SIG) n_incl_def diff_0_eq_0 diff_diff_cancel diff_is_0_eq diff_right_commute diff_self_eq_0 ofe_mono)

lift_definition upred_bupd :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<Rrightarrow>_") is
  "\<lambda>P a n. \<forall>m b. m\<le>n \<longrightarrow> valid_n (rep_comp (a,b)) m \<longrightarrow> (\<exists>c. valid_n (rep_comp (c,b)) m \<and> P c m)"
  by (meson dual_order.trans n_incl_def valid_n_incl_subst)

lift_definition upred_entails :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" is
  "\<lambda>P Q. \<forall>a n. valid_n a n \<longrightarrow> P a n \<longrightarrow> Q a n" .  
end

(* Simple definition of iprop due to the axiomatic character of our work. *)
type_synonym 'a iprop = "'a upred_f"
end