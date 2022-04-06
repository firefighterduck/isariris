theory BaseLogicShallow
imports CoreStructures
begin

subsection \<open> Uniform Predicates \<close>
text \<open> A upred formalization as a semantic subtype of functions, shallow embedding \<close>
typedef (overloaded) 'm::ucamera upred_f = "{f::('m \<Rightarrow> nat \<Rightarrow> bool). 
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
  lift_definition lim_upred_f :: "'a upred_f chain \<Rightarrow> 'a upred_f" is
    "\<lambda>(c::'a upred_f chain) (a::'a) n. \<forall>m\<le>n. n_valid a m \<longrightarrow> Rep_upred_f (Rep_chain c m) a m"
    by (smt (verit, ccfv_SIG) Rep_upred_f camera_n_incl_le camera_valid_op le_refl mem_Collect_eq 
      n_incl_def n_valid_ne order_trans)
instance apply (standard; auto simp: lim_upred_f.rep_eq n_equiv_upred_f_def; transfer)
  apply (metis (mono_tags, lifting) cr_upred_f_def n_equiv_upred_f.rep_eq nle_le rel_funD2 upred_f.pcr_cr_eq)
  by (smt (z3) Rep_upred_f cr_upred_f_def le_cases3 mem_Collect_eq n_equiv_upred_f.rep_eq 
    ne_sprop_weaken ofe_refl rel_funD2 total_n_inclI upred_f.pcr_cr_eq valid_raw_non_expansive)
end

definition map_upred_ne :: "(('b::ucamera) -n> ('a::ucamera)) \<Rightarrow> (('a upred_f) -n> ('b upred_f))" where
  "map_upred_ne (f::'b-n>'a) = Abs_ne (\<lambda>(x::'a upred_f). Abs_upred_f (\<lambda>(c::'b) n. Rep_upred_f x (Rep_ne f c) n))"

lemma upred_f_ne: "\<lbrakk>n_equiv m (P::('a::ucamera) upred_f) Q; m\<le>n; n_valid x m; Rep_upred_f P x n\<rbrakk> 
  \<Longrightarrow> Rep_upred_f Q x m"
  apply transfer using n_incl_refl by blast
  
subsubsection \<open>upred Functor\<close>
text \<open>A functor for \<^typ>\<open>'a upred_f\<close> based on sound camera morphisms.\<close>
context begin
text \<open>This is the map of the contravariant functor for uniform predicates.\<close> 
lift_definition upred_map :: "('a::ucamera,'b::ucamera) cmra_morph \<Rightarrow> 'b upred_f \<Rightarrow> 'a upred_f" is 
  "\<lambda>f P x. Rep_upred_f P (Rep_cmra_morph f x)"
  by (transfer; auto simp: n_incl_def camera_morphism_def non_expansive_def) metis

lemma upred_map_ne2: "non_expansive2 upred_map"
  by (rule non_expansive2I; transfer)
  (smt (verit, del_insts) Rep_cmra_morph Rep_upred_f camera_morphism.morphism_valid le_cases3 
    mem_Collect_eq n_equiv_cmra_morph.rep_eq n_equiv_upred_f.rep_eq ofe_sym total_n_inclI)
  
lemma upred_map_ne: "non_expansive (upred_map f)"
  by (rule non_expansive2_ne[OF upred_map_ne2])

lemma upred_morph_ne: "non_expansive (\<lambda>f. upred_map f x)"
  by (rule non_expansiveI; transfer) (auto simp: ofe_sym total_n_inclI n_equiv_cmra_morph_def)

private lemma upred_morphism: 
  "\<lbrakk>(\<And>n m x y. P x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> P y m); camera_morphism f\<rbrakk> \<Longrightarrow>
   (\<And>n m x y. (\<lambda>x. P (f x)) x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> (\<lambda>x. P (f x)) y m)"
proof -
  fix n m x y   
  assume assms1: "(\<And>n m x y. P x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> P y m)" "camera_morphism f"
  assume assms2: "(\<lambda>x. P (f x)) x n" "n_incl m x y" "m \<le> n"
  then have P: "P (f x) n" by simp
  from assms2(2) n_incl_morph[OF assms1(2)] have "n_incl m (f x) (f y)" by simp
  from assms1(1)[OF P this assms2(3)] show "(\<lambda>x. P (f x)) y m" by simp
qed

lemma Abs_morphism_inverse: "\<lbrakk>\<forall>n m x y. P x n \<longrightarrow> n_incl m x y \<longrightarrow> m \<le> n \<longrightarrow> P y m; camera_morphism f\<rbrakk> 
  \<Longrightarrow> Rep_upred_f (Abs_upred_f (\<lambda>x. P (f x))) = (\<lambda>x. P (f x))"
  by (smt (verit, best) mem_Collect_eq upred_morphism Abs_upred_f_inverse)
  
lemma upred_map_id: "upred_map id_morph P = P"
  by (auto simp: upred_map_def id_morph.rep_eq)

lemma upred_map_compose: "ofe_eq (upred_map (morph_comp g f) P) (upred_map f (upred_map g P))"
  by (simp add: morph_comp.rep_eq ofe_eq_upred_f.rep_eq upred_map.rep_eq) 

lemma upred_map_ext: "(\<forall>x. ofe_eq (Rep_cmra_morph f x) (Rep_cmra_morph g x)) \<Longrightarrow> 
  ofe_eq (upred_map f x) (upred_map g x)"
  using upred_morph_ne[unfolded non_expansive_def n_equiv_cmra_morph.rep_eq] by (metis ofe_limit)  

lift_definition upred_map_ne :: "('a::ucamera,'b::ucamera) cmra_morph \<Rightarrow> 'b upred_f -n> 'a upred_f" is
  "\<lambda>f. upred_map f" by (rule upred_map_ne)

lemma upred_map_ne_ne: "non_expansive upred_map_ne"
  by (rule non_expansiveI) 
  (smt (verit, best) n_equiv_ne.rep_eq non_expansive_def upred_map_ne.rep_eq upred_morph_ne)
end

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
then show "?sprop f \<and> ?ne f \<and> ?mon f"
  by (smt (verit, best) camera_n_incl_le ofe_mono ofe_sym order_refl upred_def_def upred_weaken 
    upred_weaken_simple)
next
assume assm: "?sprop f \<and> ?ne f \<and> ?mon f"
then show "?u f" by simp
qed

lemma upred_ne: "\<lbrakk>upred_def f; n_equiv n x y\<rbrakk> \<Longrightarrow> n_equiv n (f x n) (f y n)"
  unfolding upred_equiv_upred_f by auto

subsubsection \<open>Unifrom predicate semantics\<close>
text \<open> The semantic of uniform predicates is defined as a shallow embedding. \<close>

lift_definition upred_pure :: "bool \<Rightarrow> 'a upred_f" ("\<upharpoonleft>_") is "\<lambda>b::bool. \<lambda>_::'a. \<lambda>_::nat. b" .

lift_definition upred_eq :: "'c::ofe \<Rightarrow> 'c \<Rightarrow> 'a upred_f" (infix "=\<^sub>u" 70) is 
  "\<lambda>x (y::'c). \<lambda>_::'a. \<lambda>n. ofe_class.n_equiv n x y" by (rule ofe_mono)

lift_definition upred_conj :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<and>\<^sub>u" 60) is
  "\<lambda>P Q (a::'a) (n::nat). P a n \<and> Q a n" by (rule conj_forward)
lift_definition upred_disj :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<or>\<^sub>u" 55) is
  "\<lambda>P Q (a::'a) (n::nat). P a n \<or> Q a n" by (rule disj_forward)

lift_definition upred_impl :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixr "\<longrightarrow>\<^sub>u" 40) is
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

lift_definition upred_forall :: "('c \<Rightarrow> 'a upred_f) \<Rightarrow> 'a upred_f" (binder "\<forall>\<^sub>u" 20) is 
  "\<lambda>P (a::'a) (n::nat). \<forall>x::'c. P x a n" by (rule meta_allE)

lift_definition upred_exists :: "('c \<Rightarrow> 'a upred_f) \<Rightarrow> 'a upred_f" (binder "\<exists>\<^sub>u" 20) is 
  "\<lambda>P (a::'a) (n::nat). \<exists>x::'c. P x a n" by (rule ex_forward)

lift_definition upred_sep :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixl "\<^emph>" 60) is
  "\<lambda>P Q (a::'a) n. \<exists>b1 b2. n_equiv n a (b1 \<cdot> b2) \<and> P b1 n \<and> Q b2 n"
proof (erule exE;erule exE)
  fix P Q n m a b c1 c2
  assume assms: "n_incl m a (b::'a)" "m\<le>n"
  assume I: "n_equiv n a (op c1 c2)\<and>P c1 n\<and>Q c2 n"
  assume Q: "(\<And>n m x y. Q x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> Q y m)"
  assume "(\<And>n m x y. P x n \<Longrightarrow> n_incl m x y \<Longrightarrow> m \<le> n \<Longrightarrow> P y m)"
  then have P: "upred_def P" by auto
  from I have I': "n_equiv n a (op c1 c2)" "P c1 n" "Q c2 n" by simp_all
  from assms obtain c where c:"n_equiv m b (op a c)" using n_incl_def by blast
  from op_equiv_subst[OF this I'(1) assms(2)] have "n_equiv m b (op (op c1 c2) c)" .
  then have bc: "n_equiv m b (op c1 (op c2 c))" 
    by (metis camera_class.camera_assoc)
  from upred_weaken_simple[OF P I'(2) assms(2)] have c1: "P c1 m" .
  from Q[OF I'(3), of m, OF n_incl_op_extend assms(2), of c] have "Q (op c2 c) m" .
  with bc c1 show "\<exists>b1 b2. n_equiv m b (op b1 b2) \<and> P b1 m \<and> Q b2 m" by blast
qed

lift_definition upred_wand :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infixr "-\<^emph>" 40) is 
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
proof (unfold n_incl_def; erule exE)
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

lift_definition upred_later :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<triangleright>_" 100) is "\<lambda>P (a::'a) n. n=0 \<or> P a (n-1)" 
  by (smt (verit, ccfv_SIG) n_incl_def diff_0_eq_0 diff_diff_cancel diff_is_0_eq diff_right_commute diff_self_eq_0 ofe_mono)

lift_definition upred_bupd :: "'a upred_f \<Rightarrow> 'a upred_f" ("\<Rrightarrow>\<^sub>b_") is
  "\<lambda>P (a::'a) n. \<forall>m b. (m\<le>n \<and> n_valid (a \<cdot> b) m) \<longrightarrow> (\<exists>c. n_valid (c \<cdot> b) m \<and> P c m)"
  by (meson dual_order.trans n_incl_def n_valid_incl_subst)
  
lift_definition upred_entails :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" (infix "\<turnstile>" 50) is
  "\<lambda>P Q. \<forall>(a::'a) n. n_valid a n \<longrightarrow> P a n \<longrightarrow> Q a n" .

definition upred_entail_eq :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" (infix "\<stileturn>\<turnstile>" 40) where
  "P \<stileturn>\<turnstile> Q \<equiv> (upred_entails P Q) \<and> (upred_entails Q P)"
end

(* Basic view shift operator *)
definition upred_bvs :: "('a::ucamera) upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f" (infix "\<Rrightarrow>\<^sub>v" 70) where
  "upred_bvs P Q \<equiv> \<box>(P -\<^emph> (\<Rrightarrow>\<^sub>b Q))"
abbreviation wand_bupd (infix "==\<^emph>" 60) where "wand_bupd P Q \<equiv> P -\<^emph> \<Rrightarrow>\<^sub>b Q"  

abbreviation "upred_emp \<equiv> \<upharpoonleft>True"

declare [[coercion upred_holds, coercion_enabled = true]]

subsubsection \<open>Upred \<^const>\<open>n_equiv\<close> rules\<close>
named_theorems upred_ne_rule
lemma upred_pure_ne [upred_ne_rule]: "(x\<longleftrightarrow>y) \<Longrightarrow> n_equiv n (\<upharpoonleft>x) (\<upharpoonleft>y)" by transfer simp
lemma upred_eq_ne [upred_ne_rule]: "\<lbrakk>n_equiv n x a; n_equiv n y b\<rbrakk> \<Longrightarrow> n_equiv n (x=\<^sub>ua) (y=\<^sub>ub)"
  by transfer (auto intro: ofe_mono)
lemma upred_conj_ne [upred_ne_rule]: "\<lbrakk>n_equiv n P Q; n_equiv n R S\<rbrakk> \<Longrightarrow> n_equiv n (P\<and>\<^sub>uR) (Q\<and>\<^sub>uS)"
  by transfer simp  
lemma upred_disj_ne [upred_ne_rule]: "\<lbrakk>n_equiv n P Q; n_equiv n R S\<rbrakk> \<Longrightarrow> n_equiv n (P\<or>\<^sub>uR) (Q\<or>\<^sub>uS)"
  by transfer simp
lemma upred_impl_ne [upred_ne_rule]: "\<lbrakk>n_equiv n P Q; n_equiv n R S\<rbrakk> \<Longrightarrow> n_equiv n (P\<longrightarrow>\<^sub>uR) (Q\<longrightarrow>\<^sub>uS)"
  by transfer simp
lemma upred_forall_ne [upred_ne_rule]: "(\<And>x. n_equiv n (P x) (Q x)) \<Longrightarrow> n_equiv n (\<forall>\<^sub>u x. P x) (\<forall>\<^sub>u x. Q x)"
  by transfer' simp  
lemma upred_exists_ne [upred_ne_rule]: "(\<And>x. n_equiv n (P x) (Q x)) \<Longrightarrow> n_equiv n (\<exists>\<^sub>u x. P x) (\<exists>\<^sub>u x. Q x)"
  by transfer' simp
lemma upred_sep_ne [upred_ne_rule]: "\<lbrakk>n_equiv n P Q; n_equiv n R S\<rbrakk> \<Longrightarrow> n_equiv n (P\<^emph>R) (Q\<^emph>S)"
  by transfer (metis camera_comm camera_valid_op n_valid_ne)  
lemma upred_wand_ne [upred_ne_rule]: "\<lbrakk>n_equiv n P Q; n_equiv n R S\<rbrakk> \<Longrightarrow> n_equiv n (P-\<^emph>R) (Q-\<^emph>S)"
  by transfer (metis camera_comm camera_valid_op le_trans)  
lemma upred_own_ne [upred_ne_rule]: "n_equiv n x y \<Longrightarrow> n_equiv n (Own x) (Own y)"
  by transfer (meson n_incl_def ofe_sym op_equiv_subst)
lemma upred_valid_ne [upred_ne_rule]: "n_equiv n x y \<Longrightarrow> n_equiv n (\<V> x) (\<V> y)"
  apply transfer using camera_props(8) n_equiv_sprop_def by blast
lemma upred_persis_ne [upred_ne_rule]: "n_equiv n P Q \<Longrightarrow> n_equiv n (\<box>P) (\<box>Q)"
  by transfer (metis camera_core_n_valid)  
lemma upred_plain_ne [upred_ne_rule]: "n_equiv n P Q \<Longrightarrow> n_equiv n (\<^item>P) (\<^item>Q)"  
  apply transfer using \<epsilon>_n_valid by blast
lemma upred_later_ne: "n_equiv n P Q \<Longrightarrow> n_equiv n (\<triangleright>P) (\<triangleright>Q)"
  apply transfer by (meson diff_le_self dual_order.trans ne_sprop_weaken ofe_eq_limit valid_raw_non_expansive)
lemma upred_later_contr: "contractive upred_later"
  unfolding contractive_def apply transfer
  by (smt (verit, best) One_nat_def Rep_sprop Suc_pred bot_nat_0.not_eq_extremum diff_le_mono diff_le_self less_Suc_eq_le mem_Collect_eq nle_le)
lemma upred_bupd_ne [upred_ne_rule]: "n_equiv n P Q \<Longrightarrow> n_equiv n (\<Rrightarrow>\<^sub>bP) (\<Rrightarrow>\<^sub>bQ)"
  by transfer (meson camera_valid_op order_trans)
end