theory DemoSetup
imports 
  BruteForceAutomation 
  "../HeapLang/Notation"
  "../IrisCore/Misc"
  "../IrisCore/AuthHeap"
begin

context
includes heap_syntax
fixes get_inv :: "gname \<Rightarrow> 'res :: ucamera \<Rightarrow> inv option"
  and put_inv
  and get_heap :: "gname \<Rightarrow> 'res \<Rightarrow> heap_lang_heap option"
  and put_heap
  and get_proph :: "gname \<Rightarrow> 'res \<Rightarrow> (proph_id, val\<times>val) proph_mapGS option"
  and put_proph
assumes inv_inG[inv_inG_axiom]: "inG get_inv put_inv"
  and heap_inG[heap_inG_axiom]: "inG get_heap put_heap"
  and prophm_inG[proph_inG_axiom]: "inG get_proph put_proph"
begin

lemmas wp_inG[inG_axioms] = inv_inG heap_inG prophm_inG

definition diaframe_hint :: "'res upred_f \<Rightarrow> ('b \<Rightarrow> 'res upred_f) \<Rightarrow> ('res upred_f \<Rightarrow> 'res upred_f) \<Rightarrow> ('a \<Rightarrow> 'res upred_f) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'res upred_f) \<Rightarrow> bool" where
  "diaframe_hint H L M A U \<equiv> \<forall>y::'b. (H \<^emph> L y \<turnstile> M (\<exists>\<^sub>u x::'a. A x \<^emph> U y x))"

lemma hintE: "diaframe_hint H L M A U \<Longrightarrow> (\<And>y::'b. (H \<^emph> L y \<turnstile> M (\<exists>\<^sub>u x::'a. A x \<^emph> U y x)))"
  unfolding diaframe_hint_def by simp
  
lemma inv_hint: "diaframe_hint upred_emp (\<lambda>x::'a. \<triangleright>(L x)) (ViewShift.linear_fupd put_inv E)
  (\<lambda>x::'a. inv put_inv N (L x)) (\<lambda>_ x::'a. inv put_inv N (L x))"
  apply (auto simp: diaframe_hint_def)
  apply (iMod rule: inv_alloc[OF inv_inG, to_entailment])
  apply iExistsR2
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF persistent_dupl]])
  apply pers_solver apply (rule inv_inG)
  apply (rule upred_frame)
  by simp

lemma biabd_hint_apply_aux: 
  assumes "diaframe_hint H L (ViewShift.fancy_upd put_inv E3 E2) A U"
  shows "H \<^emph> ViewShift.fancy_upd put_inv E1 E3 (\<exists>\<^sub>u y. L y \<^emph> (\<forall>\<^sub>u x. (U y x) -\<^emph> (G x))) 
    \<turnstile> ViewShift.fancy_upd put_inv E1 E2 (\<exists>\<^sub>u x. G x \<^emph> A x)"
  apply (entails_substR rule: fupd_mask_trans[OF inv_inG, of _ E3])
  apply (iMod rule: fupd_frame_r[OF inv_inG, where ?R=H])
  apply iExistsL
  apply (iApply rule: hintE[OF assms])
  apply (iMod rule: fupd_frame_r[OF inv_inG, where ?R="(\<forall>\<^sub>ux. U _ x -\<^emph> G x)"])
  apply iExistsL subgoal for y x
  apply (iExistsR x)
  apply (move_sepL "\<forall>\<^sub>u x::'b. ?P x")
  apply (rule pull_forall_antecedent')
  apply (rule upred_entails_trans[OF upred_forall_inst[of _ x]])
  apply iApply_wand
  by iFrame_single
  done
  
lemma biabd_hint_apply: 
assumes "diaframe_hint H L (ViewShift.fancy_upd put_inv E3 E2) A U" 
  "\<Delta> \<turnstile> ViewShift.fancy_upd put_inv E1 E3 (\<exists>\<^sub>u y. L y \<^emph> (\<forall>\<^sub>u x. (U y x) -\<^emph> (G x)))"
shows "\<Delta> \<^emph> H \<turnstile> ViewShift.fancy_upd put_inv E1 E2 (\<exists>\<^sub>u x. G x \<^emph> A x)"
proof -
  from biabd_hint_apply_aux[OF assms(1)] 
  have aux: "(ViewShift.fancy_upd put_inv E1 E3(\<exists>\<^sub>u y. L y \<^emph> (\<forall>\<^sub>u x. (U y x) -\<^emph> (G x)))) \<^emph> H 
    \<turnstile> (ViewShift.fancy_upd put_inv E1 E2(\<exists>\<^sub>ux. G x \<^emph> A x))"
    apply (subst (2) upred_sep_comm) by simp
  show ?thesis
    apply (rule upred_entails_trans[OF upred_sep_mono[OF assms(2) upred_entails_refl[of H]]])
    by (rule aux)
qed

lemma biabd_hint_apply': 
assumes "diaframe_hint H L (ViewShift.fancy_upd put_inv E3 E2) (\<lambda>_. A) (\<lambda>y _. U y)" 
  "\<Delta> \<turnstile> ViewShift.fancy_upd put_inv E1 E3 (\<exists>\<^sub>u y. L y \<^emph> ((U y) -\<^emph> G))"
shows "\<Delta> \<^emph> H \<turnstile> ViewShift.fancy_upd put_inv E1 E2 (G \<^emph> A)"
proof -
  from assms(2) have "\<Delta> \<turnstile> fancy_upd'' put_inv E1 E3 (\<exists>\<^sub>u y. L y \<^emph> (\<forall>\<^sub>u x. ((\<lambda>y _. U y) y x) -\<^emph> G))" 
    by (simp add: drop_forall)
  from biabd_hint_apply[OF assms(1) this, unfolded drop_exists] show ?thesis .
qed
  
lemma wp_store_hint:
  "diaframe_hint upred_emp (\<lambda>_. ViewShift.fancy_upd put_inv UNIV E (\<exists>\<^sub>u v'. (\<triangleright>(AuthHeap.points_to_full put_heap l v')) \<^emph> 
  (\<triangleright>((ViewShift.wand_fupd put_inv (AuthHeap.points_to_full put_heap l v) E UNIV (\<Phi> #[()]))))))
  (ViewShift.linear_fupd put_inv UNIV) (\<lambda>_. WeakestPrecondition.WP put_inv put_heap put_proph (Store #[l] (Val v)) \<Phi>) (\<lambda>_ _. upred_emp)"
  unfolding diaframe_hint_def
  apply (simp add: drop_exists emp_rule)
  apply (entails_substR rule: fupd_intro[OF inv_inG])
  apply (rule elim_modal_entails[OF elim_modal_fupd_wp_atomic[OF wp_inG atomic_store]])
  apply iExistsL
  apply (move_sepL "\<triangleright>(AuthHeap.points_to_full put_heap ?l ?v)")  
  apply later_elim
  apply (rule wp_store'[OF wp_inG, unfolded to_val_simp])
  apply (rule upred_later_mono_extL)
  apply (rule upred_entails_trans[OF _ wp_value[OF wp_inG]])
  by iApply_wand

lemmas store_hint = biabd_hint_apply'[OF wp_store_hint]

declare upred_later_exists[iris_simp]
declare upred_entails_trans[OF store_hint[where ?G = upred_emp, unfolded emp_rule to_val_simp] fupd_wp, wp_symbolic_execution_steps]
declare frame_baseL[frame_rule]
end
end