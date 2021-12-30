theory BaseLogicShallow
imports CoreStructures
begin

subsection \<open> Uniform Predicates \<close>
text \<open> A  upred formalization as a semantic subtype of functions, shallow embedding \<close>
typedef (overloaded) 'm upred_f = "{f::('m::ucamera \<Rightarrow> nat \<Rightarrow> bool). 
  \<forall>n m x y. f x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> f y m}"
  proof
  define uTrue where "uTrue \<equiv> \<lambda>x::'m. \<lambda>n::nat. True"
  hence "\<forall>n m x y. uTrue x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> uTrue y m" by fast
  thus "uTrue \<in> {f. \<forall>n m x y. f x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> f y m}" by blast
qed

setup_lifting type_definition_upred_f
lemmas [simp] = Rep_upred_f_inverse Rep_upred_f_inject
lemmas [simp, intro!] = Rep_upred_f[unfolded mem_Collect_eq]

instantiation upred_f :: (ucamera) ofe begin
  lift_definition n_equiv_upred_f :: "nat \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" is
    "\<lambda>n P Q. \<forall>a m. m\<le>n \<longrightarrow> n_valid a m \<longrightarrow> (P a m \<longleftrightarrow> Q a m)" .
  lift_definition ofe_eq_upred_f :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" is 
    "\<lambda>P Q. \<forall>a n. n_valid a n \<longrightarrow> (P a n \<longleftrightarrow> Q a n)" .
instance by (standard) (auto simp: n_equiv_upred_f.rep_eq ofe_eq_upred_f.rep_eq)
end
instantiation upred_f :: (ucamera) cofe begin
  lift_definition lim_upred_f :: "(nat \<Rightarrow> 'a upred_f) \<Rightarrow> 'a upred_f" is
    "\<lambda>c a n. \<forall>m\<le>n. n_valid a m \<longrightarrow> c m a m" 
    by (meson n_incl_def camera_valid_op dual_order.trans ne_sprop_weaken ofe_mono order_refl valid_raw_non_expansive)
instance by (standard; auto simp: is_chain_def; transfer; auto)
  (meson le_refl ne_sprop_weaken ofe_refl total_n_inclI valid_raw_non_expansive)
end

lemma upred_f_ne: "\<lbrakk>n_equiv m (P::('a::ucamera) upred_f) Q; m\<le>n; n_valid x m; Rep_upred_f Q x n\<rbrakk> 
  \<Longrightarrow> Rep_upred_f Q x m"
  by (transfer; auto simp: n_incl_def) (metis \<epsilon>_left_id camera_comm ofe_refl) 


text \<open> Basic predicates and predicate connectives: \<close>
(* Arcane Isabelle magic, presented to you by Manuel Eberl *)
context assumes "SORT_CONSTRAINT('a::ucamera)"
begin

text \<open> upred as a predicate on functions\<close>
definition upred_def :: "('a \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> bool" where 
  [simp]: "upred_def P \<equiv> \<forall>n m x y. P x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> P y m"
lemma upred_defI[intro?]: 
  assumes "\<And>n m x y. \<lbrakk>P x n; n_incl m x y; m\<le>n\<rbrakk> \<Longrightarrow> P y m"
  shows "upred_def P"
  using assms by auto

lemma upred_def_rep: "upred_def (Rep_upred_f f)" using Rep_upred_f upred_def_def by blast

lemma upred_weaken: "\<lbrakk>n_equiv n x y; m\<le>n;upred_def f; f x n\<rbrakk> \<Longrightarrow> f y m"
  using Rep_upred_f total_n_inclI upred_def_def by fast

lemma upred_weaken_simple: "\<lbrakk>upred_def f; f x n; m\<le>n\<rbrakk> \<Longrightarrow> f x m"
  using ofe_refl upred_weaken by blast 

lift_definition upred_holds :: "'a upred_f \<Rightarrow> bool" is
  "\<lambda>u. \<forall>a n. n_valid a n \<longrightarrow>  u a n" .
  
(* This shows that upred_f are pointwise down-closed, non-expansive and monotone. *)
theorem upred_equiv_upred_f: 
  "upred_def f \<longleftrightarrow> 
  ((\<forall>x n m. m \<le> n \<longrightarrow> f x n \<longrightarrow> f x m) \<and>
  (\<forall>n x y. n_equiv n x y\<longrightarrow>(\<forall>m\<le>n. f x m \<longleftrightarrow> f y m)) \<and>
  (\<forall>n x y. n_incl n x y \<longrightarrow> (\<forall>m\<le>n. f x m \<longrightarrow> f y m)))" 
(is "?u f \<longleftrightarrow> (?sprop f \<and> ?ne f \<and> ?mon f)")
proof
assume assm: "?u f"
then show "?sprop f \<and> ?ne f \<and> ?mon f" apply auto
  using total_n_inclI apply blast
  apply (meson total_n_inclI ofe_sym order_refl)
  by (meson camera_n_incl_le order_refl total_n_inclI)
next
assume assm: "?sprop f \<and> ?ne f \<and> ?mon f"
show "?u f" by (simp add: assm)
qed

lemma upred_ne: "\<lbrakk>upred_def f; n_equiv n x y\<rbrakk> \<Longrightarrow> n_equiv n (f x n) (f y n)"
  unfolding upred_equiv_upred_f by auto
  
text \<open> The semantic of uniform predicates is defined as a shallow embedding. \<close>

lift_definition upred_pure :: "bool \<Rightarrow> 'a upred_f" ("\<upharpoonleft>_") is "\<lambda>b::bool. \<lambda>_::'a. \<lambda>_::nat. b" .

lift_definition upred_eq :: "'c::ofe \<Rightarrow> 'c \<Rightarrow> 'a upred_f" (infix "=\<^sub>u" 60) is 
  "\<lambda>x (y::'c). \<lambda>_::'a. \<lambda>n. ofe_class.n_equiv n x y" by (rule ofe_mono)

lift_definition upred_conj :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<and>\<^sub>u" 60) is
  "\<lambda>P Q (a::'a) (n::nat). P a n \<and> Q a n" by (rule conj_forward)
lift_definition upred_disj :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<or>\<^sub>u" 60) is
  "\<lambda>P Q (a::'a) (n::nat). P a n \<or> Q a n" by (rule disj_forward)

lift_definition upred_impl :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixr "\<longrightarrow>\<^sub>u" 60) is
  "\<lambda>P Q (a::'a) n. (\<forall>m\<le>n. \<forall>b. incl a b \<longrightarrow> n_valid b m \<longrightarrow> P b m \<longrightarrow> Q b m)"
proof -
  fix x y n n' a b m c
  assume assms: "n_incl n' a (b::'a)" "n'\<le>n" "m\<le>n'" "incl b c" "n_valid c m" "x c m" 
  assume x_upred: "(\<And>n m x' y. x x' n \<Longrightarrow> n_incl m x' y \<Longrightarrow> m \<le> n \<Longrightarrow> x y m)"
  assume y_upred: "(\<And>n m x (y'::'a). y x n \<Longrightarrow> n_incl m x y' \<Longrightarrow> m \<le> n \<Longrightarrow> y y' m)"
  assume I: "(\<And>m b. m \<le> n \<Longrightarrow> incl a b \<Longrightarrow> n_valid b m \<Longrightarrow> x b m \<Longrightarrow> y b m)"
  from \<open>n_incl n' a b\<close> obtain b' where b': "n_equiv n' b (op a b')" using n_incl_def by blast
  from \<open>incl b c\<close> obtain c' where c':"c = op b c'" using incl_def by blast
  with assms have "n_valid (op b c') m" by simp
  with b' have vabc: "n_valid (op (op a b') c') m" 
    by (meson assms(3) valid_op_op_weaken ofe_mono)
  from c' \<open>x c m\<close> have xbc':"x (op b c') m"  by simp
  have bc_abc: "n_equiv m (op b c') (op (op a b') c')" 
    using ofe_class.ofe_mono[OF assms(3) op_equiv[OF b', of c' c', simplified ofe_class.ofe_refl, simplified]] .
  from upred_weaken[OF this, of m, simplified] x_upred xbc'
  have xabc: "x (op (op a b') c') m" by metis
  from bc_abc c' have "n_equiv m (op (op a b') c') c" by (simp add:ofe_class.ofe_sym)
  from upred_weaken[OF this, of m, simplified, of y] have yabc: "y (op (op a b') c') m \<Longrightarrow> y c m" 
    using y_upred by blast
  have "incl a (op (op a b') c')" using incl_op_extend incl_def by blast  
  from yabc[OF I[OF order.trans[OF assms(3,2)] this vabc xabc]]
  show "y c m".
qed

lift_definition upred_forall :: "('c \<Rightarrow> 'a upred_f) \<Rightarrow> 'a upred_f" ("\<forall>\<^sub>u _") is 
  "\<lambda>P (a::'a) (n::nat). \<forall>x::'c. P x a n" by (rule meta_allE)

lift_definition upred_exists :: "('c \<Rightarrow> 'a upred_f) \<Rightarrow> 'a upred_f" ("\<exists>\<^sub>u _") is 
  "\<lambda>P (a::'a) (n::nat). \<exists>x::'c. P x a n" by (rule ex_forward)

lift_definition upred_sep :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<^emph>" 80) is
  "\<lambda>P Q (a::'a) n. \<exists>b1 b2. n_equiv n a (b1 \<cdot> b2) \<and> P b1 n \<and> Q b2 n"
proof auto
  fix P Q n m a b c1 c2
  assume assms: "n_incl m a (b::'a)" "m\<le>n"
  assume I: "n_equiv n a (op c1 c2)" "P c1 n" "Q c2 n"
  assume Q: "(\<And>n m x y. Q x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> Q y m)"
  assume "(\<And>n m x y. P x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> P y m)"
  then have P: "upred_def P" by auto
  from assms obtain c where c:"n_equiv m b (op a c)" using n_incl_def by blast
  from op_equiv_subst[OF this I(1) assms(2)] have "n_equiv m b (op (op c1 c2) c)" .
  then have bc: "n_equiv m b (op c1 (op c2 c))" 
    by (metis camera_class.camera_assoc)
  from upred_weaken_simple[OF P I(2) assms(2)] have c1: "P c1 m" .
  from Q[OF I(3), of m, OF n_incl_op_extend assms(2), of c] have "Q (op c2 c) m" .
  with bc c1 show "\<exists>b1 b2. n_equiv m b (op b1 b2) \<and> P b1 m \<and> Q b2 m" by blast
qed

lift_definition upred_wand :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixr "-\<^emph>" 60) is 
  "\<lambda>P Q (a::'a) n. \<forall>b m. m\<le>n \<longrightarrow> n_valid (a \<cdot> b) m \<longrightarrow> P b m \<longrightarrow> Q (a \<cdot> b) m"
proof -
  fix P Q n n' a b c m
  assume Q: "\<And>n m x y. Q (x::'a) n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> Q y m"
  assume I: "(\<And>b m. m\<le>n \<Longrightarrow> n_valid (op a b) m \<Longrightarrow> P b m \<Longrightarrow> Q (op a b) m)"
  assume assms: "n_incl n' a (b::'a)" "n'\<le>n" "m\<le>n'" " n_valid (op b c) m" "P c m"
  from assms have "m\<le>n" by linarith
  from Q[OF I[OF this n_valid_incl_subst[OF assms(1,4,3)] assms(5)] n_incl_extend[OF assms(1,3)] order.refl]
  show "Q (op b c) m" .
qed

lift_definition upred_own :: "'a \<Rightarrow> 'a upred_f" ("Own(_)") is "\<lambda>(a::'a) b n. n_incl n a b" 
unfolding n_incl_def using camera_assoc op_equiv_subst by metis

lift_definition upred_valid :: "'b::camera \<Rightarrow> 'a upred_f" ("\<V>(_)") is "\<lambda>(a::'b) (_::'a). n_valid a" 
  using Rep_sprop n_incl_def by blast
  
lift_definition upred_persis :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<box>_") is "\<lambda>P (a::'a) n. (P (core a) n)::bool"
proof (auto simp: n_incl_def)
  fix f n m 
  fix a b c :: 'a
  assume I: "\<And>n m x y. f (x::'a) n \<Longrightarrow> \<exists>c. n_equiv m y (op x c) \<Longrightarrow> m \<le> n \<Longrightarrow> f y m"
  assume assms: "f (core a) n" "m\<le>n" "n_equiv m b (op a c)"
  then have "\<exists>d. n_equiv m b (op a d)" by auto
  then have "\<exists>d. n_equiv m (core b) (op (core a) d)" 
    by (metis incl_def camera_core_mono core_ne[unfolded non_expansive_def])
  from I[OF assms(1) this assms(2)] show "f (core b) m" .
qed

lift_definition upred_plain :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<^item>_") is "\<lambda>P (_::'a) (n::nat). (P (\<epsilon>::'a) n)::bool"
  by (metis \<epsilon>_left_id ofe_eq_limit n_incl_def)

lift_definition upred_later :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<triangleright>_") is "\<lambda>P (a::'a) n. n=0 \<or> P a (n-1)" 
  by (smt (verit, ccfv_SIG) n_incl_def diff_0_eq_0 diff_diff_cancel diff_is_0_eq diff_right_commute diff_self_eq_0 ofe_mono)

lift_definition upred_bupd :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<Rrightarrow>_") is
  "\<lambda>P (a::'a) n. \<forall>m b. m\<le>n \<longrightarrow> n_valid (a \<cdot> b) m \<longrightarrow> (\<exists>c. n_valid (c \<cdot> b) m \<and> P c m)"
  by (meson dual_order.trans n_incl_def n_valid_incl_subst)

lift_definition upred_entails :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" (infix "\<turnstile>" 50) is
  "\<lambda>P Q. \<forall>(a::'a) n. n_valid a n \<longrightarrow> P a n \<longrightarrow> Q a n" .

definition upred_entail_eq :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" (infix "\<stileturn>\<turnstile>" 40) where
  "P \<stileturn>\<turnstile> Q \<equiv> (upred_entails P Q) \<and> (upred_entails Q P)"
end

text \<open> Basic properties of upred predicates: \<close>

lemma upred_entail_eq_simp: "P\<stileturn>\<turnstile>Q \<equiv> \<forall>a n. n_valid a n \<longrightarrow> Rep_upred_f P a n = Rep_upred_f Q a n"
  by (auto simp: upred_entail_eq_def upred_entails.rep_eq) (smt (verit, best))
lemma upred_entail_eqE: "P\<stileturn>\<turnstile>Q \<Longrightarrow> (\<And>a n. n_valid a n \<Longrightarrow> Rep_upred_f P a n = Rep_upred_f Q a n)"
  using upred_entail_eq_simp by auto
lemma upred_entail_eqI: "(\<And>a n. n_valid a n \<Longrightarrow> Rep_upred_f P a n = Rep_upred_f Q a n) \<Longrightarrow> P\<stileturn>\<turnstile>Q"
  using upred_entail_eq_simp by auto

lemma upred_entail_eq_symm: "P\<stileturn>\<turnstile>Q \<Longrightarrow> Q\<stileturn>\<turnstile>P"
  by (auto simp: upred_entail_eq_def)
  
lemma upred_entail_eqL: "P\<stileturn>\<turnstile>Q \<Longrightarrow> P\<turnstile>Q" by (simp add: upred_entail_eq_def)
lemma upred_entail_eqR: "P\<stileturn>\<turnstile>Q \<Longrightarrow> Q\<turnstile>P" by (simp add: upred_entail_eq_def)

lemma upred_entails_trans: "\<lbrakk>P\<turnstile>Q; Q\<turnstile>R\<rbrakk> \<Longrightarrow> P\<turnstile>R"
  by (auto simp: upred_entails.rep_eq)

lemma upred_entails_refl [simp]: "P\<turnstile>P" by (auto simp: upred_entails_def)

lemma own_valid: "Own(a) \<turnstile> \<V>(a)"
  apply (auto simp: upred_entails.rep_eq upred_own.rep_eq upred_valid.rep_eq n_incl_def)
  using camera_valid_op n_valid_ne by blast

lemma upred_holds_entails: "upred_holds P \<longleftrightarrow> ((\<upharpoonleft>True) \<turnstile> P)"
  by (auto simp: upred_holds.rep_eq upred_entails.rep_eq upred_pure.rep_eq)

lemma upred_entailsE: "P \<turnstile> Q \<Longrightarrow> (\<And>a n. \<lbrakk>n_valid a n; Rep_upred_f P a n\<rbrakk> \<Longrightarrow> Rep_upred_f Q a n)"
  by (auto simp: upred_entails.rep_eq)

lemma upred_wandI: "(P \<^emph> Q) \<turnstile> R \<Longrightarrow> P \<turnstile> (Q-\<^emph>R)"
  apply (auto simp: upred_entails.rep_eq upred_sep.rep_eq upred_wand.rep_eq)
  using ofe_refl upred_def_rep upred_weaken_simple by blast
lemma upred_wandE: "P \<turnstile> (Q-\<^emph>R) \<Longrightarrow> (P \<^emph> Q) \<turnstile> R"
  by transfer (meson camera_valid_op dual_order.refl n_valid_ne ofe_sym total_n_inclI)

lemma upred_true_sep: "(P \<^emph> \<upharpoonleft>True) = P"
  apply transfer using n_incl_def by fastforce

lemma upred_sep_comm: "P \<^emph> Q = Q \<^emph> P"
  by transfer (metis (no_types, opaque_lifting) camera_comm)

lemma upred_sep_mono: "\<lbrakk>P1\<turnstile>Q;P2\<turnstile>R\<rbrakk> \<Longrightarrow> P1\<^emph>P2\<turnstile>Q\<^emph>R"
  by transfer (metis camera_comm camera_valid_op n_valid_ne)

lemma upred_sep_pure: "\<lbrakk>P\<turnstile>Q;P\<turnstile>\<upharpoonleft>b\<rbrakk> \<Longrightarrow> P\<turnstile>Q\<^emph>\<upharpoonleft>b"
  by transfer (meson n_incl_def n_incl_refl)

lemma upred_wand_holdsI: "Q \<turnstile> R \<Longrightarrow> upred_holds (Q-\<^emph>R)"
  by (metis upred_wandI upred_holds_entails upred_true_sep upred_sep_comm)
lemma upred_wand_holdsE: "upred_holds (Q-\<^emph>R) \<Longrightarrow> Q \<turnstile> R"
  by transfer (metis \<epsilon>_left_id camera_valid_op dual_order.refl)

lemma upred_own_core_persis: "Own(a) \<turnstile> \<box>Own(core a)"
  by (auto simp: upred_entails.rep_eq upred_own.rep_eq upred_persis.rep_eq camera_core_mono_n)

lemma upred_entails_wand_holdsL: "\<lbrakk>P \<turnstile> Q; upred_holds (Q-\<^emph>R)\<rbrakk> \<Longrightarrow> upred_holds (P-\<^emph>R)"
  by transfer (metis camera_comm camera_valid_op)

lemma upred_entails_wand_holdsR: "\<lbrakk>Q \<turnstile> R; upred_holds (P-\<^emph>Q)\<rbrakk> \<Longrightarrow> upred_holds (P-\<^emph>R)"
  by transfer auto

lemma upred_entails_wand_holdsR2: "\<lbrakk>Q \<turnstile> R; upred_holds (P1-\<^emph>P2-\<^emph>Q)\<rbrakk> \<Longrightarrow> upred_holds (P1-\<^emph>P2-\<^emph>R)"
  by transfer auto

lemma pure_entailsI: "(p \<Longrightarrow> q) \<Longrightarrow> \<upharpoonleft>p\<turnstile>\<upharpoonleft>q"
  by (auto simp: upred_pure_def upred_entails.rep_eq Abs_upred_f_inverse)

lemma discrete_valid: "\<V>(a::'a::dcamera) \<stileturn>\<turnstile> \<upharpoonleft>(valid a)"
  apply (rule upred_entail_eqI; auto simp: upred_valid.rep_eq upred_pure.rep_eq)
  using dcamera_valid_iff by blast+

lemma own_op: "Own(a\<cdot>b) \<stileturn>\<turnstile> Own(a) \<^emph> Own(b)"
  apply (rule upred_entail_eqI)
  apply (auto simp: upred_own.rep_eq upred_sep.rep_eq)
  apply (metis camera_assoc n_incl_def n_incl_op_extend n_incl_refl)
  by (smt (z3) camera_assoc camera_comm n_incl_def ofe_trans op_equiv)

lemma own_valid2: "upred_holds (Own(a1) -\<^emph> Own (a2) -\<^emph> \<V>(a1\<cdot>a2))"
  apply (rule upred_wand_holdsI)
  apply (rule upred_wandI)
  using own_op own_valid upred_entails_trans upred_entail_eq_def by blast

lemma entails_pure_extend: "\<lbrakk>P\<turnstile>\<upharpoonleft>b;b \<Longrightarrow> P\<turnstile>Q\<rbrakk> \<Longrightarrow> P\<turnstile>Q"
  by transfer blast

lemma upred_wand_holds2I: "P\<^emph>Q\<turnstile>R \<Longrightarrow> upred_holds (P -\<^emph> Q -\<^emph> R)"
  apply (rule upred_wand_holdsI)
  apply (rule upred_wandI)
  by assumption
lemma upred_wand_holds2E: "upred_holds (P -\<^emph> Q -\<^emph> R) \<Longrightarrow> P\<^emph>Q\<turnstile>R"
  apply (rule upred_wandE)  
  apply (rule upred_wand_holdsE)
  by assumption
  
(* Simple definition of iprop due to the axiomatic character of our work. *)
type_synonym 'a iprop = "'a upred_f"

text \<open> Persistent predicates \<close>
definition persistent :: "('a::ucamera) iprop \<Rightarrow> bool" where "persistent P \<equiv> P \<turnstile> \<box>P"

lemma persistent_persis: "persistent (\<box>P)"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq camera_core_idem)

lemma persistent_pure: "persistent (\<upharpoonleft>P)"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_pure.rep_eq)  

lemma persistent_valid: "persistent (\<V>(a))"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_valid.rep_eq)

lemma persistent_core_own: "persistent (Own(a::'a::{core_id,ucamera}))"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_own.rep_eq core_id)  
end