theory BruteForceAutomation
imports "../HeapLang/WeakestPrecondition"
begin       

subsection \<open>Brute auto automation\<close>
(*
  General idea: iterate over all hypotheses (i.e. all single "'res::ucamera upred_f" terms connected by separating
  conjunctions), move them to the top and try all rules in a brute force auto approach.
  Only backtrack to the next hypothesis if there is nothing that can be done for the
  current hypothesis (plus goal).
  
  It might help to use a normal form of sorts (similarly to Diaframe) but we try to make this 
  approach work without such an extra step.
*)

named_theorems lock_inG_axiom

subsubsection \<open>Rule setup\<close>
text \<open>All rules operate directly on the top level hypothesis.\<close>

lemmas normalize_hyps = upred_entails_substE[OF upred_entail_eqL[OF upred_later_sep], unfolded upred_sep_assoc_eq]

lemmas intro_rules = upred_wandI upred_wand_holdsI

lemmas single_goal_framing = upred_entails_refl upred_entails_trans[OF upred_weakeningR split_last_frame]
  split_last_frame

lemmas multi_goal_framing = upred_frame framing'' framing'

lemmas single_hyp_framing = upred_wand_goal framing

lemmas pure_goal_lifting = upred_pureI upred_sep_pure
lemmas pure_hypothesis_lifting = upred_pure_impl

lemmas fupd_elim_hyps = elim_modal_entails'[OF elim_modal_fupd]
  elim_modal_entails[OF elim_modal_fupd]
  elim_modal_entails[OF elim_modal_fupd_wp_atomic]
  elim_modal_entails'[OF elim_modal_fupd_wp_atomic]

lemmas bupd_elim = upred_entails_trans[OF upd_fupd[to_entailment]]
  upred_entails_substE[OF upd_fupd[to_entailment]]
  
lemmas later_elim_hyps = upred_later_mono_extR upred_later_mono
  elim_modal_entails'[OF elim_modal_timeless']
  elim_modal_entails[OF elim_modal_timeless']
  upred_entails_trans[OF upred_entail_eqR[OF upred_later_sep] upred_later_mono]

lemmas existential_elim_hyps = upred_existsE_ext upred_existsE'

lemmas existential_elim_goal = upred_exists_lift[OF exI] upred_exists_lift'[OF exI]

lemmas universal_elim_goal = upred_forallI

named_theorems wp_symbolic_execution_steps 
lemmas [wp_symbolic_execution_steps] = upred_entails_trans[OF _ wp_pure_step_later[OF _ _ _ pure_exec_beta, simplified]]
  upred_entails_trans[OF _  wp_pure_step_later[OF _ _ _ pure_exec_fst, simplified]] 
  upred_entails_trans[OF _ wp_pure_step_later[OF _ _ _ pure_exec_snd, simplified]] 
  wp_load wp_let_bind' wp_alloc' wp_store' upred_entails_trans[OF _ wp_value]
  
lemmas additional_simps = upred_exists_eq_sep upred_exists_eq_sep' upred_pure_sep_conj' 
  upred_exists_eq_sepR upred_exists_eq_sepR' subst'_def upred_holds_entails
declare additional_simps[iris_simp]

lemmas last_resort_drop_goal_modality = upred_persis_mono[where ?P=upred_emp, unfolded emp_rule]
  upred_entails_trans[OF _ upred_laterI] upred_entails_trans[OF _ fupd_intro[to_entailment]]
  upred_entails_trans[OF _ upred_entails_trans[OF upred_laterI upred_entail_eqL[OF upred_later_sep]]]
  existential_elim_goal

named_theorems alloc_rule 
lemmas [alloc_rule] =
  frame_rule_apply[OF upred_entails_trans[OF fupd_mono[OF _ upred_entails_trans[OF upred_exist_mono[OF inv_alloc[to_entailment]] fupd_exists_lift]] fupd_mask_trans]]
  frame_rule_apply[OF upred_entails_trans[OF fupd_mono[OF _ inv_alloc[to_entailment]] fupd_mask_trans]]

subsubsection \<open>Brute auto iteration methods\<close>

method allocate =
  rule alloc_rule, (fast intro: frame_rule inv_inG_axiom)+, iris_simp?, is_entailment

method framing =
  ((rule single_hyp_framing, fast intro: frame_rule inv_inG_axiom, iris_simp?)
  | auto simp: iris_simp intro!: log_prog_rule single_goal_framing multi_goal_framing);
  is_entailment

method open_inv=
  (rule upred_entails_substE[OF inv_acc[OF _ subset_UNIV, to_entailment]], rule inv_inG_axiom,  
    rule fupd_frame_mono, iris_simp)
  | (rule upred_entails_trans[OF inv_acc[OF _ subset_UNIV, to_entailment]], rule inv_inG_axiom, 
    rule fupd_mono, iris_simp)

method last_resort = 
  (allocate
  | (reshape_wp?, step intro: last_resort_drop_goal_modality wp_symbolic_execution_steps;
      ((rule inv_inG_axiom heap_inG_axiom proph_inG_axiom)+)?)
  | (rule framing_emp, fast intro!: log_prog_rule, is_entailment))
  
text \<open>Try all possible rules and steps for the given hypothesis.\<close>
method brute_force_hyp =
  (auto simp: iris_simp 
  intro!: pure_goal_lifting universal_elim_goal existential_elim_hyps upred_universal_wand normalize_hyps
    intro_rules fupd_elim_hyps(1,2)[OF inv_inG_axiom] fupd_elim_hyps
    bupd_elim[OF inv_inG_axiom] later_elim_hyps(1,2) pure_hypothesis_lifting
  intro: log_prog_rule heap_inG_axiom lock_inG_axiom later_elim_hyps(3-5)
  | framing | open_inv)
    
text \<open>Apply brute auto search to all hypotheses by destructuring the antecedent.\<close>
method brute_force_hyps for hyps :: "'res::ucamera upred_f" =
  match (hyps) in "rest\<^emph>hyp" for rest hyp :: "'res::ucamera upred_f" \<Rightarrow> 
    \<open>(move_sepL hyp, brute_force_hyp) | brute_force_hyps rest\<close>
  \<bar> _ \<Rightarrow> \<open>(move_sepL hyps, brute_force_hyp) | last_resort\<close>

text \<open>Get the antecedent from the conclusion entailment term and start the iteration process.\<close>
method iterate_hyps_safe for concl_trm :: bool =
  match (concl_trm) in "hyps\<turnstile>_" for hyps :: "'res::ucamera upred_f" \<Rightarrow> \<open>brute_force_hyps hyps\<close>

text \<open>Iterate over the hypotheses and apply possible rules in a brute auto manner.\<close>
method iterate_hyps = iris_simp; 
  (fast intro: inG_axioms 
  | get_concl "BruteForceAutomation.iterate_hyps_safe")

method brute_force_solver = repeat_new \<open>iterate_hyps\<close>


lemma lambda_to_ectxt: "f$x$y = lang_ctxt (FI (AppLCtx y)) (f$x)"
  by auto

lemma lambda_to_ectxt': "f$x = lang_ctxt (FI (AppLCtx x)) (f)"
  by auto  

lemma lambda_to_ectxt_arg: "f$x = lang_ctxt (FI (AppRCtx f)) x"
  by auto

lemma BetaS'[intro]: "e' = subst' x v2  e1 \<Longrightarrow> ((Val(RecV None x e1))$(Val v2)) \<sigma> [] \<Rightarrow>\<^sub>h e' \<sigma> []"
  by (rule BetaS) (auto simp: subst'_def)

lemma pure_exec_lambda_beta: "pure_exec True 1 ((Val (V\<lambda> x: b))$(Val y)) (subst' x y b)"
  apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
  using BetaS' apply auto by (smt (verit, best) expr.inject(1) headE(5) val.inject(2))

lemma pure_exec_rec: "pure_exec True 1 ((E\<lambda> x: b)) (V\<lambda> x : b)"
  apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
  using RecS by blast+

lemma pure_exec_val: "pure_exec True 0 (Val v) (Val v)"
  by (auto simp: zero_steps)

lemma pure_exec_unop_neg: "pure_exec True 1 (UnOp NegOp TrueE) (FalseE)"
  apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
  using UnOpS un_op_eval.simps(1) by fastforce+
  
method cleanup_texan_apply =
  match conclusion in "_ \<turnstile> ((\<triangleright>(\<forall>\<^sub>u v. _ v)) :: 'res::ucamera upred_f)" \<Rightarrow> \<open>iNext, iIntros\<close>
  
method iwp uses rule = reshape_wp_cleanup?, match rule[uncurry] in 
  "_ \<Longrightarrow> upred_holds (WeakestPrecondition.texan2 _ _ _ _ _ _ _ _ :: 'res::ucamera upred_f)" \<Rightarrow>
    \<open>(entails_substR rule: texan_apply[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom 
      rule[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom], simplified iris_simp, simplified] 
    | entails_substR rule: texan2_apply[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom 
      rule[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom], simplified iris_simp, simplified]),
    iris_simp, cleanup_texan_apply?\<close>
  \<bar> "upred_holds (WeakestPrecondition.texan2 _ _ _ _ _ _ _ _ :: 'res::ucamera upred_f)" \<Rightarrow>
    \<open>(entails_substR rule: texan_apply[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom rule, simplified iris_simp, simplified]
    | entails_substR rule: texan2_apply[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom rule, simplified iris_simp, simplified]),
    iris_simp, cleanup_texan_apply?\<close>
  \<bar> _ \<Rightarrow> \<open>entails_substR rule: rule[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom, simplified]\<close>
  \<bar> _ \<Rightarrow> \<open>entails_substR rule: rule[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom, simplified]\<close>,
  reshape_wp_cleanup?

method iwp_val = iwp rule: wp_value

method iwp_pure uses rule = iwp rule: wp_pure[OF _ _ _ rule, simplified]
  
method iwp_pure_later uses rule = iwp rule: wp_pure_step_later[OF _ _ _ rule, simplified]

method iwp_beta = reshape_wp_cleanup?, match conclusion in 
  "_ \<turnstile> (wp _ _ _ _ _ ((LamE _ _ ) $ _) _ :: 'res::ucamera upred_f)" \<Rightarrow> 
    \<open>
    subst (1) lambda_to_ectxt', entails_substR rule: wp_bind[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom]
      ,iwp_pure rule: pure_exec_rec,
    iwp_val, subst lang_ctxt.simps, unfold fill_item.simps, 
    iwp_pure rule: pure_exec_lambda_beta, simp add: subst'_def del: lang_ctxt.simps
    \<close>
  \<bar> "_ \<turnstile> (wp _ _ _ _ _ (Val (LamV _ _ ) $ _) _ :: 'res::ucamera upred_f)" \<Rightarrow> 
    \<open>iwp_pure rule: pure_exec_lambda_beta, simp add: subst'_def del: lang_ctxt.simps\<close>
  \<bar> _ \<Rightarrow> fail

method iwp_beta_later = reshape_wp?, match conclusion in 
  "_ \<turnstile> (wp _ _ _ _ _ ((LamE _ _ ) $ _) _ :: 'res::ucamera upred_f)" \<Rightarrow> 
    \<open>
    subst (1) lambda_to_ectxt', entails_substR rule: wp_bind[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom]
      ,iwp_pure rule: pure_exec_rec,
    iwp_val, subst lang_ctxt.simps, unfold fill_item.simps, 
    iwp_pure_later rule: pure_exec_lambda_beta, auto simp: subst'_def simp del: lang_ctxt.simps
    \<close>
  \<bar> "_ \<turnstile> (wp _ _ _ _ _ (Val (LamV _ _ ) $ _) _ :: 'res::ucamera upred_f)" \<Rightarrow> 
    \<open>iwp_pure_later rule: pure_exec_lambda_beta, auto simp: subst'_def simp del: lang_ctxt.simps\<close>
  \<bar> _ \<Rightarrow> fail

method fold_app = match conclusion in 
  "_ \<turnstile> wp _ _ _ _ _ (Val _) 
  (\<lambda>v. wp _ _ _ _ _ (lang_ctxt (FI (AppRCtx _)) (Val v)) _  :: 'res::ucamera upred_f)" \<Rightarrow>
    \<open>iwp_val, (subst lang_ctxt.simps, unfold fill_item.simps)+\<close>
\<bar> "_ \<turnstile> wp _ _ _ _ _ (Val _) 
  (\<lambda>v. wp _ _ _ _ _ (fill [AppRCtx _] (Val v)) _  :: 'res::ucamera upred_f)" \<Rightarrow>
    \<open>iwp_val, (subst lang_ctxt.simps, unfold fill_item.simps)+\<close>
  
method iwp_seq = unfold lambda_to_ectxt_arg, (entails_substR rule: wp_bind[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom])+, fold_app?  

method iwp_bind = reshape_wp,
  entails_substR rule: wp_bind[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom],
  iris_simp
end