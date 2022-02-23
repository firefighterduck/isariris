theory WeakestPrecondition
imports "../IrisCore/Invariant" Notation LanguageDefs
begin

subsection \<open>Weakest Preconditions\<close>
 
function wp :: "stuckness \<Rightarrow> mask \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> iprop) \<Rightarrow> iprop" where
  "wp s E e1 \<Phi> = (case HeapLang.to_val e1 of Some v \<Rightarrow> \<Turnstile>{E}=> (\<Phi> v)
    | None \<Rightarrow> (\<forall>\<^sub>u \<sigma>1 \<kappa> \<kappa>s.
      ((state_interp \<sigma>1 (\<kappa>@\<kappa>s)) ={E,Set.empty}=\<^emph>
        ((\<upharpoonleft>(case s of NotStuck \<Rightarrow> reducible e1 \<sigma>1 | _ \<Rightarrow> True)) \<^emph>
        (\<forall>\<^sub>u e2 \<sigma>2 efs. ((\<upharpoonleft>(prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs))
          ={Set.empty}\<triangleright>=\<^emph> (\<Turnstile>{Set.empty,E}=> ((state_interp \<sigma>2 \<kappa>s) \<^emph>
            (wp s E e2 \<Phi>) \<^emph> ([\<^emph>\<^sub>l:] efs (\<lambda>ef. wp s UNIV ef (\<lambda>_. upred_emp)))))))))))"
by auto

abbreviation WP :: "expr \<Rightarrow> (val \<Rightarrow> iprop) \<Rightarrow> iprop" ("WP _ {{ _ }}") where
  "WP e {{ \<Phi> }} \<equiv> wp NotStuck {} e \<Phi>"

text \<open>
  First we show that all basic properties of wp hold for inputs in the domain, then we 
  always assume all values to lie in the domain.
\<close>
context begin
lemma wp_value_fupd: 
assumes "wp_dom (s, E, Val v, P)"
shows "wp s E (of_val v) P \<stileturn>\<turnstile> \<Turnstile>{E}=> P v"
  by (auto simp: wp.psimps[OF assms])

lemma wp_value: 
assumes "wp_dom (s, E, Val v, P)"
shows "P v \<turnstile> wp s E (Val v) P"
  by (auto simp: wp.psimps[OF assms] fupd_intro upred_wand_holdsE)

lemma wp_fupd_helper: "\<forall>\<^sub>u v. (upred_emp ={E}=\<^emph> upred_emp)"
  apply (subst upred_holds_entails)
  apply (rule upred_forallI)
  using fupd_intro upred_holds_entails by auto
  
lemma wp_strong_mono: 
assumes "\<And>E1 e P. wp_dom (s1, E1, e, P)" "\<And>E2 e Q. wp_dom (s2, E2, e, Q)"
  "s1 \<le> s2" 
shows "\<forall>\<^sub>uE1 E2 e P Q. (\<upharpoonleft>(E1 \<subseteq> E2)) \<longrightarrow>\<^sub>u (wp s1 E1 e P -\<^emph> (\<forall>\<^sub>u v. (P v ={E2}=\<^emph> Q v)) -\<^emph> wp s2 E2 e Q)"
  (is "upred_holds ?goal")  
  apply (rule loebI)
  apply (auto intro!: upred_forallI upred_implI_pure upred_wandI)
  subgoal for E1 E2 e P Q
  apply (subst wp.psimps[OF assms(1)[of E1]])
  apply (subst wp.psimps[OF assms(2)[of E2]])
  apply (cases "HeapLang.to_val e")
  apply auto
  apply (auto intro!: upred_forallI upred_wandI)
    subgoal for \<sigma>1 \<kappa> \<kappa>s
    apply (rule add_holds[OF fupd_mask_subseteq], assumption)
    apply (rule upred_entails_trans[OF _ fupd_mask_trans[of E2 E1]])
    apply (rule fupd_frame_mono)
    apply (rule upred_entails_trans[OF upred_sep_comm2R])
    apply (rule upred_entails_trans[OF upred_sep_comm4_2])
    apply (rule upred_entails_trans[OF upred_sep_comm3M])
    apply (rule upred_entails_trans[OF upred_sep_comm2R])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<sigma>1]])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<kappa>]])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<kappa>s]])
    apply (rule upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
    apply (rule upred_entails_trans[OF _ fupd_mask_trans[of E1 "{}"]])
    apply (rule fupd_frame_mono)
    apply (simp add: upred_sep_assoc_eq)
    apply (rule upred_entails_trans[OF upred_sep_comm2R])
    apply (rule upred_pure_impl)
    apply (rule upred_entails_trans[OF _ fupd_empty])
    apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm]])
    apply (rule upred_sep_pure)
    apply (auto intro!: upred_forallI upred_wandI upred_pure_impl)
    subgoal for e2 \<sigma>2 efs
      apply (rule upred_entails_substE[OF upred_forall_inst[of _ e2]])
      apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<sigma>2]])
      apply (rule upred_entails_substE[OF upred_forall_inst[of _ efs]])
      apply simp
      apply (rule upred_entails_substE[OF upred_true_wand])
      apply (rule upred_entails_trans[OF upred_sep_comm3L])
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_trans[OF upred_sep_comm2R])
      apply (rule upred_entails_substE[OF upred_entail_eqL[OF upred_persis_later]])
      apply (rule upred_entails_trans[OF upred_sep_comm2R])
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_trans[OF upred_sep_comm3L])
      apply (rule fupd_frame_mono)
      apply (rule upred_entails_trans[OF upred_sep_comm3L])
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], unfolded upred_sep_assoc_eq])
      apply (rule upred_later_mono_extR)
      apply (simp add: upred_sep_assoc_eq)
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_trans[OF upred_sep_comm3L])
      apply (rule fupd_frame_mono)
      apply (rule upred_entails_trans[OF _ fupd_mask_trans[of "{}" E1]])
      apply (rule fupd_frame_mono)
      apply (simp add: upred_sep_assoc_eq)
      apply (rule upred_entails_trans[OF _ fupd_mono[OF upred_entails_eq[OF upred_sep_comm2L]]])
      apply (rule upred_entails_trans[OF _ fupd_mono[OF upred_sep_comm2R]])
      apply (rule upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_frame_r]])
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_trans[OF upred_sep_comm2R])
      apply (rule upred_frame)
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_trans[OF upred_sep_comm2R])
      apply (auto simp: upred_true_sep intro!: fupd_frame_mono)
      apply (rule split_frame[of _ "(\<box> ?goal) \<^emph> _ \<^emph> _"  "(\<box> ?goal) \<^emph> [\<^emph>\<^sub>l:] efs \<lambda>x. wp s1 UNIV x (\<lambda>_. upred_emp)"])
      apply (rule can_be_split_sepR)
      apply (rule can_be_split_sepL)
      apply (rule can_be_split_sepL)
      apply (rule persistent_dupl', pers_solver)
      apply (rule can_be_split_refl)
      subgoal 
        apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
        apply (rule upred_entails_trans[OF upred_sep_comm2R])
        apply (rule upred_entails_substE[OF upred_persisE])
        apply (rule upred_entails_substE[OF upred_forall_inst[of _ E1]])
        apply (rule upred_entails_substE[OF upred_forall_inst[of _ E2]])
        apply (rule upred_entails_substE[OF upred_forall_inst[of _ e2]])
        apply (rule upred_entails_substE[OF upred_forall_inst[of _ P]])
        apply (rule upred_entails_substE[OF upred_forall_inst[of _ Q]])
        by (auto intro!: upred_entails_substE[OF upred_entail_eqL[OF upred_emp_impl]]
          upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq]
          upred_entails_trans[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
      apply (rule upred_wandE)
      apply (rule upred_entails_trans[OF _ upred_wand_holdsE[OF sep_emp_map_list_entails']])
      apply (rule upred_persis_mono)
      apply (rule upred_entails_trans[OF upred_forall_inst[of _ UNIV]])
      apply (rule upred_entails_trans[OF upred_forall_inst[of _ UNIV]])
      apply (rule upred_forallI)
      subgoal for x
      apply (rule upred_entails_trans[OF upred_forall_inst[of _ x]])
      apply (rule upred_entails_trans[OF upred_forall_inst[of _ "(\<lambda>_. upred_emp)"]])
      apply (rule upred_entails_trans[OF upred_forall_inst[of _ "(\<lambda>_. upred_emp)"]])
      apply (auto intro!: upred_entails_trans[OF upred_entail_eqL[OF upred_emp_impl]])
      apply (rule upred_wandI)
      apply (subst upred_sep_comm)
      apply (rule upred_entails_trans[OF upred_wand_apply])
      apply (rule add_holds[OF wp_fupd_helper])
      apply (subst upred_sep_comm)
      by (auto intro: upred_entails_trans[OF upred_wand_apply])
      done
    apply (rule upred_pureI)
    using assms(3)
    apply (cases s1; cases s2)
    by auto
  subgoal for v
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ v]])
    apply (rule upred_wandE)
    apply (rule upred_entails_trans[OF _ fupd_ext])
  by (auto intro!: upred_entails_trans[OF upred_weakeningR] upred_wand_holdsE[OF fupd_mask_mono])
  done
done

lemma fupd_wp: 
assumes "wp_dom (s, E, e, P)"
shows "\<Turnstile>{E}=> (wp s E e P) \<turnstile> wp s E e P"
  unfolding wp.psimps[OF assms]
  apply (cases "HeapLang.to_val e")
  apply auto
  apply (auto intro!: upred_forallI)
  subgoal for \<sigma>1 \<kappa> \<kappa>s
    apply (rule upred_wandI)
    apply (rule upred_entails_trans[OF _ fupd_mask_trans[of E E]])
    apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
    apply (rule fupd_frame_mono)
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<sigma>1]])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<kappa>]])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<kappa>s]])
    by (auto intro: upred_entails_trans[OF upred_wand_apply])
  by (simp add: fupd_mask_trans)

lemma wp_fupd:
assumes "\<And>E e P. wp_dom (s, E, e, P)"
shows "wp s E e (\<lambda>v. \<Turnstile>{E}=> P v) \<turnstile> wp s E e P"
  apply (rule add_holds[OF wp_strong_mono[OF assms assms, simplified]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ E]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ E]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ e]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ "(\<lambda>v. \<Turnstile>{E}=> P v)"]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ P]])
  apply (auto intro!: upred_entails_substE[OF upred_entail_eqL[OF upred_emp_impl]]
    upred_entails_trans[OF upred_wand_apply])
  apply (rule add_holds[OF upred_holds_forall[OF fupd_mask_mono[of E E, simplified], of P]])
  apply (subst upred_sep_comm)
  by (rule upred_wand_apply)
  
lemma wp_mono:
assumes "\<And>E e P. wp_dom (s, E, e, P)" "(\<And>v. P v \<turnstile> Q v)"
shows "wp s E e P \<turnstile> wp s E e Q"
  apply (rule add_holds[OF wp_strong_mono[OF assms(1) assms(1), simplified]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ E]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ E]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ e]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ P]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ Q]])
  apply (auto intro!: upred_entails_substE[OF upred_entail_eqL[OF upred_emp_impl]]
    upred_entails_trans[OF upred_wand_apply])
  apply (rule add_holds[OF upred_holds_forall[OF fupd_intro'[OF assms(2), of _ E]], of _ id, simplified])
  apply (subst upred_sep_comm)
  by (rule upred_wand_apply)
end

lemma wp_dom_axiom [simp]: "wp_dom (s E e P)" sorry

lemma wp_atomic: "atomic (stuckness_to_atomicity s) e \<Longrightarrow>
  \<Turnstile>{E1,E2}=> wp s E2 e (\<lambda>v. \<Turnstile>{E2,E1}=> P v) \<turnstile> wp s E1 e P" sorry

lemma wp_bind: "wp s E e (\<lambda>v. wp s E (lang_ctxt K (of_val v)) P) \<turnstile> wp s E (lang_ctxt K e) P" sorry
lemma wp_bind_inv: "wp s E (lang_ctxt K e) P \<turnstile> wp s E e (\<lambda>v. wp s E (lang_ctxt K (of_val v)) P)" sorry
lemma wp_stuck_mono: "s1 \<le> s2 \<Longrightarrow> wp s1 E e P \<turnstile> wp s2 E e P" sorry
lemma wp_stuck_weaken: "wp s E e P \<turnstile> wp MaybeStuck E e P" using wp_stuck_mono[of s MaybeStuck] by simp
lemma wp_frame: "P \<^emph> wp s E e (\<lambda>v. Q v) \<turnstile> wp s E e (\<lambda>v. P \<^emph> Q v)" sorry

lemma wp_frame_step:
assumes "HeapLang.to_val e = None" "E2\<subseteq>E1"
shows "(\<Turnstile>{E1}[E2]\<triangleright>=> Q) \<^emph> wp s E2 e (\<lambda>v. P v) \<turnstile> wp s E1 e (\<lambda>v. P v \<^emph> Q)" 
  sorry

lemma wp_frame_step':
assumes "HeapLang.to_val e = None"
shows "(\<triangleright>Q) \<^emph> wp s E e (\<lambda>v. P v) \<turnstile> wp s E e (\<lambda>v. P v \<^emph> Q)"
  sorry
  
lemma wp_lift_step_fupdN: 
assumes "HeapLang.to_val e1 = None"
shows "(\<forall>\<^sub>u \<sigma>1 \<kappa> \<kappa>s. ((state_interp \<sigma>1 (\<kappa>@\<kappa>s)) ={E,Set.empty}=\<^emph>
  ((\<upharpoonleft>(case s of NotStuck \<Rightarrow> red e1 \<sigma>1 | _ \<Rightarrow> True)) \<^emph>
  (\<forall>\<^sub>u e2 \<sigma>2 efs. ((\<upharpoonleft>(prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs)) ={Set.empty}\<triangleright>=\<^emph> 
    (\<Turnstile>{Set.empty,E}=> ((state_interp \<sigma>2 \<kappa>s) \<^emph>
      (wp s E e2 \<Phi>) \<^emph> ([\<^emph>\<^sub>l:] efs (\<lambda>ef. wp s UNIV ef (\<lambda>_. upred_emp))))))))))
   \<turnstile> wp s E e1 \<Phi>" sorry
end   