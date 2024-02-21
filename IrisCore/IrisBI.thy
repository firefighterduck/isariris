theory IrisBI
imports "../BICore/BIInterface" "UpredLattice"
begin

interpretation iris_bi: bi_later upred_entails upred_emp upred_pure upred_conj upred_disj upred_impl
  upred_forall upred_exists upred_sep upred_wand upred_persis upred_later
  apply unfold_locales
  subgoal by simp
  subgoal by simp
  subgoal by (erule upred_entails_trans, assumption)
  subgoal by (simp add: upred_entail_eq_ofe[symmetric] upred_entail_eq_def)
  subgoal by (rule non_expansiveI, rule upred_ne_rule, simp)
  subgoal by (rule non_expansive2I, rule upred_ne_rule; simp)
  subgoal by (rule non_expansive2I, rule upred_ne_rule; simp)
  subgoal by (rule non_expansive2I, rule upred_ne_rule; simp)
  subgoal by (rule non_expansiveI, rule upred_ne_rule, simp add: n_equiv_fun_def)
  subgoal by (rule non_expansiveI, rule upred_ne_rule, simp add: n_equiv_fun_def)
  subgoal by (rule non_expansive2I, rule upred_ne_rule; simp)
  subgoal by (rule non_expansive2I, rule upred_ne_rule; simp)
  subgoal by simp
  subgoal for b by (cases b) auto
  subgoal by (rule upred_weakeningL')
  subgoal by (rule upred_weakeningR')
  subgoal by (erule upred_entails_conjI, assumption)
  subgoal by (rule upred_disjIL, simp)
  subgoal by (rule upred_disjIR, simp)
  subgoal by (erule upred_disjE, assumption)
  subgoal by (erule upred_implI)
  subgoal by (erule upred_implI')
  subgoal by (rule upred_forallI, simp)
  subgoal by (rule upred_forall_inst)
  subgoal by (rule upred_existsI', simp)
  subgoal by (erule upred_existsE)
  subgoal by (erule upred_sep_mono, assumption)
  subgoal by (simp add: emp_rule)
  subgoal by (simp add: emp_rule)
  subgoal by (simp add: upred_sep_comm)
  subgoal by (rule upred_sep_assoc_rev)
  subgoal by (erule upred_wandI)
  subgoal by (erule upred_wandE)
  subgoal by (rule non_expansiveI, rule upred_ne_rule, simp)
  subgoal by (erule upred_persis_mono)
  subgoal by (rule upred_persis_idem)
  subgoal by (simp add: upred_persis_upred_emp)
  subgoal by transfer blast
  subgoal by transfer blast
  subgoal by (rule upred_weakeningL)
  subgoal by (simp add: persis_conj_sepL persistent_persis upred_frame upred_persisE)
  subgoal by (rule non_expansiveI, rule upred_ne_rule, simp)
  subgoal by (rule upred_later_mono)
  subgoal by (rule upred_laterI)
  subgoal by transfer blast
  subgoal by transfer blast
  subgoal by (rule upred_entail_eqL[OF upred_later_sep])
  subgoal by (rule upred_entail_eqR[OF upred_later_sep])
  subgoal by (rule upred_entail_eqR[OF upred_persis_later])
  subgoal by (rule upred_entail_eqL[OF upred_persis_later])
  apply transfer using incl_n_incl by blast

lemma "upred_holds = iris_bi.bi_holds"
  unfolding iris_bi.bi_holds_def using upred_holds_entails by blast
end