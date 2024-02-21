theory UpredLattice
imports Automation
begin

subsubsection \<open>upred_f lattice\<close>

instantiation upred_f :: (ucamera) Sup begin
lift_definition Sup_upred_f :: "'a::ucamera upred_f set \<Rightarrow> 'a upred_f" is
  "\<lambda>S a n. \<exists>f\<in>S. f a n" by metis
instance ..
end

instantiation upred_f :: (ucamera) Inf begin
lift_definition Inf_upred_f :: "'a::ucamera upred_f set \<Rightarrow> 'a upred_f" is
  "\<lambda>S a n. \<forall>f\<in>S. f a n" by metis
instance ..
end

instantiation upred_f :: (ucamera) order begin
(* It would be nicer to use entailment here, but this doesn't work as entailment is only leq for 
  valid camera objects. *)
lift_definition less_eq_upred_f :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" is 
  "\<lambda>P Q. (\<forall>(a::'a) n. \<forall>m\<le>n. P a n \<longrightarrow> Q a m)" .
definition less_upred_f :: "'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" where 
  "less_upred_f P Q = (P \<le> Q \<and> \<not>(Q \<le> P))"
instance apply standard 
  apply (auto simp: less_upred_f_def less_eq_upred_f_def)
  apply transfer 
  apply (meson dual_order.refl)
  apply transfer
  apply (rule HOL.ext)+
  apply auto
  by blast+
end

lemma leq_entails: "P \<le> Q \<Longrightarrow> P \<turnstile> Q"
  apply transfer apply auto by (metis order_eq_refl)

lemma sep_leq_mono: "P \<le> Q \<Longrightarrow> P\<^emph>R \<le> Q\<^emph>R"
  apply transfer apply auto by (meson n_incl_refl ofe_mono) 
  
context inG begin
lemma own_op_le: "(own upd_cmra \<gamma> (a\<cdot>b)) \<le> (own upd_cmra \<gamma> a \<^emph> own upd_cmra \<gamma> b)"
  unfolding own_def
  apply (auto simp: less_eq_upred_f.rep_eq upred_own.rep_eq upred_sep.rep_eq return_op)
  by (metis camera_assoc n_incl_def n_incl_op_extend n_incl_refl ofe_mono) 
lemma own_op_le2: "(own upd_cmra \<gamma> (a\<cdot>b)) \<ge> (own upd_cmra \<gamma> a \<^emph> own upd_cmra \<gamma> b)"
  unfolding own_def
  apply (auto simp: less_eq_upred_f.rep_eq upred_own.rep_eq upred_sep.rep_eq return_op)
  proof -
  fix aa :: 'a and n :: nat and m :: nat and b1 :: 'a and b2 :: 'a
  assume a1: "m \<le> n"
  assume a2: "n_incl n (return_cmra \<gamma> b) b2"
  assume a3: "n_incl n (return_cmra \<gamma> a) b1"
  assume a4: "n_equiv n aa (b1 \<cdot> b2)"
  obtain aaa :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "\<forall>x0 x1 x2. (\<exists>v3. n_equiv x2 x0 (x1 \<cdot> v3)) = n_equiv x2 x0 (x1 \<cdot> aaa x0 x1 x2)" by moura
  then have f5: "\<forall>n a aa. (\<not> n_incl n a aa \<or> n_equiv n aa (a \<cdot> aaa aa a n)) \<and> (n_incl n a aa \<or> 
    (\<forall>ab. \<not> n_equiv n aa (a \<cdot> ab)))"
  using n_incl_def by blast
  then have "n_equiv m aa (return_cmra \<gamma> b \<cdot> aaa b2 (return_cmra \<gamma> b) n \<cdot> (return_cmra \<gamma> a \<cdot> 
    aaa b1 (return_cmra \<gamma> a) n))"
  using a4 a3 a2 a1 by (smt (z3) camera_comm camera_props(10) ofe_down_contr ofe_trans)
  then show "n_incl m (return_cmra \<gamma> a \<cdot> return_cmra \<gamma> b) aa"
  using f5 by (smt (z3) camera_assoc camera_comm)
  qed 
end

instantiation upred_f :: (ucamera) lattice begin
definition inf_upred_f where [simp]: "inf_upred_f \<equiv> upred_conj"
definition sup_upred_f where [simp]: "sup_upred_f \<equiv> upred_disj"
instance apply standard 
  apply (auto simp: less_upred_f_def less_eq_upred_f_def iris_simp)
  apply (transfer, fastforce)
  apply (transfer, fastforce)
  apply (transfer, fastforce)
  apply (transfer, fastforce)
  apply (transfer, fastforce)
  by (transfer, metis)
end

instantiation upred_f :: (ucamera) complete_lattice begin
definition bot_upred_f :: "'a upred_f" where "bot_upred_f = \<upharpoonleft>False"
definition top_upred_f :: "'a upred_f" where "top_upred_f = \<upharpoonleft>True"
instance
apply standard
apply (auto simp: less_eq_upred_f_def less_upred_f_def bot_upred_f_def top_upred_f_def)
subgoal apply transfer by (metis n_incl_refl)
subgoal apply transfer by (smt (verit, ccfv_SIG))
subgoal apply transfer by (meson n_incl_refl)
subgoal apply transfer by (smt (verit, best))
subgoal apply transfer by simp
subgoal apply transfer by simp
done
end

(* An experiment to overcome the unfortunate leq definition for upred_f. 
  If we take the quotient with regard to ofe_eq, i.e. equality is only up to valid camera objects,
  then we get that leq can be entailment.*)
quotient_type (overloaded) 'a upred = "'a::ucamera upred_f" / ofe_eq
  apply (auto simp: equivp_def)
  using ofe_limit ofe_sym ofe_trans' apply blast
  by (simp add: ofe_eq_eq)

instantiation upred :: (ucamera) complete_lattice begin
lift_definition Inf_upred :: "'a upred set \<Rightarrow> 'a upred" is "Inf::'a upred_f set \<Rightarrow> 'a upred_f" 
  apply (auto simp: Inf_upred_f.rep_eq ofe_eq_upred_f.rep_eq)
  apply (meson ofe_eq_upred_f.rep_eq rel_setD2)
  by (meson ofe_eq_upred_f.rep_eq rel_set_def)
lift_definition Sup_upred :: "'a upred set \<Rightarrow> 'a upred" is "Sup::'a upred_f set \<Rightarrow> 'a upred_f" 
  apply (auto simp: Sup_upred_f.rep_eq ofe_eq_upred_f.rep_eq)
  apply (meson ofe_eq_upred_f.rep_eq rel_setD1)
  by (meson ofe_eq_upred_f.rep_eq rel_setD2)
lift_definition bot_upred :: "'a upred" is "bot::'a upred_f" .
lift_definition top_upred :: "'a upred" is "top::'a upred_f" .
lift_definition inf_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" is "upred_conj"
  by transfer auto
lift_definition sup_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" is "upred_disj"
  by transfer auto
lift_definition less_eq_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> bool" is "upred_entails"
  by transfer auto
definition less_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> bool" where 
  "less_upred P Q = (P \<le> Q \<and> \<not>(Q \<le> P))"
instance proof
fix x y :: "'a upred" show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (simp add: less_upred_def)
next
fix x :: "'a upred" show "x \<le> x" by (transfer, rule upred_entails_refl)
next
fix x y z :: "'a upred" show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (transfer, rule upred_entails_trans)
next
fix x y :: "'a upred" show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" 
  by (transfer, simp add: upred_entail_eq_ofe[unfolded upred_entail_eq_def, symmetric])
next
fix x y :: "'a upred" show "inf x y \<le> x" by (transfer, rule upred_weakeningL')
next
fix x y :: "'a upred" show "inf x y \<le> y" by (transfer, rule upred_weakeningR')
next
fix x y z :: "'a upred" show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z" by (transfer, rule upred_entails_conjI)
next
fix x y :: "'a upred" show "x \<le> sup x y" by (transfer, rule upred_disjIL, iris_simp)
next
fix y x :: "'a upred" show "y \<le> sup x y" by (transfer, rule upred_disjIR, iris_simp)
next
fix y x z :: "'a upred" show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x" by (transfer, rule upred_disjE)
next
fix x :: "'a upred" and A assume "x\<in>A" 
then have "Inf (rep_upred ` A) \<turnstile> rep_upred x" by (auto simp: Inf_upred_f.rep_eq upred_entails.rep_eq)
then show "Inf A \<le> x" apply (auto simp: Inf_upred_def less_eq_upred_def)
using Quotient3_upred[unfolded Quotient3_def] by (smt (verit, best) less_eq_upred.abs_eq)
next
fix z :: "'a upred" and A assume "\<And>x. x \<in> A \<Longrightarrow> z \<le> x" 
then have "\<forall>x\<in>A. rep_upred z \<turnstile> rep_upred x" by (auto simp: less_eq_upred_def)
then have "rep_upred z \<turnstile> Inf (rep_upred ` A)" apply (auto simp: Inf_upred_f_def upred_entails_def) 
  by (smt (verit) Rep_upred_f mem_Collect_eq Abs_upred_f_inverse)
then show "z \<le> Inf A" apply (auto simp: Inf_upred_def less_eq_upred_def)
using Quotient3_upred[unfolded Quotient3_def] by (smt (verit, best) less_eq_upred.abs_eq)
next
fix x :: "'a upred" and A assume "x \<in> A"
then have "rep_upred x \<turnstile> Sup (rep_upred ` A)" by (auto simp: Sup_upred_f.rep_eq upred_entails.rep_eq)
then show "x \<le> Sup A" apply (auto simp: Sup_upred_def less_eq_upred_def)
using Quotient3_upred[unfolded Quotient3_def] by (smt (verit, best) less_eq_upred.abs_eq)
next
fix z  :: "'a upred" and A assume "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
then have "\<forall>x\<in>A. rep_upred x \<turnstile> rep_upred z" by (auto simp: less_eq_upred_def)
then have "Sup (rep_upred ` A) \<turnstile> rep_upred z" apply (auto simp: Sup_upred_f_def upred_entails_def) 
  by (smt (verit) Rep_upred_f mem_Collect_eq Abs_upred_f_inverse)
then show "Sup A \<le> z" apply (auto simp: Sup_upred_def less_eq_upred_def)
using Quotient3_upred[unfolded Quotient3_def] by (smt (verit, best) less_eq_upred.abs_eq)
next
show "Inf {} = (top :: 'a upred)" apply transfer unfolding top_upred_f_def apply transfer by simp
next
show "Sup {} = (bot :: 'a upred)" apply transfer unfolding bot_upred_f_def apply transfer by simp
qed
end


subsubsection \<open>A custom lattice definition for upred_f\<close>
named_theorems upred_lattice
lift_definition uSup:: "'a::ucamera upred_f set \<Rightarrow> 'a upred_f" is "\<lambda>S a n. \<exists>f\<in>S. f a n"
 by metis
lift_definition uInf :: "'a::ucamera upred_f set \<Rightarrow> 'a upred_f" is
  "\<lambda>S a n. \<forall>f\<in>S. f a n" by metis
definition uless_eq :: "'a::ucamera upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" (infix "\<le>\<^sub>u" 50) where 
  [upred_lattice]: "uless_eq = (\<turnstile>)"
definition uless :: "'a::ucamera upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" (infix "<\<^sub>u" 50) where 
  "uless P Q = (P \<le>\<^sub>u Q \<and> \<not>(Q \<le>\<^sub>u P))"
definition uinf where [upred_lattice]: "uinf \<equiv> upred_conj"
definition usup where [upred_lattice]: "usup \<equiv> upred_disj"
definition ubot :: "'a::ucamera upred_f" where [upred_lattice]: "ubot = \<upharpoonleft>False"
definition utop :: "'a::ucamera upred_f" where [upred_lattice]: "utop = \<upharpoonleft>True"

lemma sup_entails: "P \<turnstile> Q \<Longrightarrow> P \<turnstile> uSup {P. P \<turnstile> Q}"
  by transfer blast

text \<open>The properties of an order are automatically proven.\<close>
declare uless_def[upred_lattice] upred_entails_trans[upred_lattice]
   upred_entail_eqI[unfolded upred_entail_eq_ofe, upred_lattice]

method usimp = simp add: upred_lattice

text \<open>The properties of a lattice\<close>
lemma [upred_lattice]: "uinf x y \<le>\<^sub>u x" apply usimp by (rule upred_weakeningL')
lemma [upred_lattice]: "uinf x y \<le>\<^sub>u y" apply usimp by (rule upred_weakeningR')
lemma [upred_lattice]: "x \<le>\<^sub>u y \<Longrightarrow> x \<le>\<^sub>u z \<Longrightarrow> x \<le>\<^sub>u uinf y z" apply usimp by (rule upred_entails_conjI)
lemma [upred_lattice]: "x \<le>\<^sub>u usup x y" apply usimp by (rule upred_disjIL[OF upred_entails_refl])
lemma [upred_lattice]: "y \<le>\<^sub>u usup x y" apply usimp by (rule upred_disjIR[OF upred_entails_refl])
lemma [upred_lattice]: "y \<le>\<^sub>u x \<Longrightarrow> z \<le>\<^sub>u x \<Longrightarrow> usup y z \<le>\<^sub>u x" apply usimp by (rule upred_disjE)

text \<open>The properties of a complete lattice\<close>
lemma uInf_lower [upred_lattice]: "x \<in> A \<Longrightarrow> uInf A \<le>\<^sub>u x" apply usimp apply transfer by fast
lemma uInf_greatest [upred_lattice]: "(\<And>x. x \<in> A \<Longrightarrow> z \<le>\<^sub>u x) \<Longrightarrow> z \<le>\<^sub>u uInf A" apply usimp apply transfer by metis
lemma uSup_upper [upred_lattice]: "x \<in> A \<Longrightarrow> x \<le>\<^sub>u uSup A" apply usimp apply transfer by blast
lemma uSup_least [upred_lattice]: "(\<And>x. x \<in> A \<Longrightarrow> x \<le>\<^sub>u z) \<Longrightarrow> uSup A \<le>\<^sub>u z" apply usimp apply transfer by metis
lemma uInf_empty [upred_lattice]: "uInf {} = utop" apply usimp apply transfer by simp
lemma uSup_empty [upred_lattice]: "uSup {} = ubot" apply usimp apply transfer by simp
end