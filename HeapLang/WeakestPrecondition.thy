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
  "WP e {{ \<Phi> }} \<equiv> wp NotStuck UNIV e \<Phi>"

text \<open>
  First we show that some basic properties of wp hold for inputs in the domain, then we 
  always assume that all values lie in the domain.
\<close>
locale wp_rules =
  assumes wp_dom_axiom: "wp_dom (s, E, e, P)"
begin

lemmas wp_simp = wp.psimps[OF wp_dom_axiom]

lemma wp_value_fupd: "wp s E (of_val v) P \<stileturn>\<turnstile> \<Turnstile>{E}=> P v"
  by (auto simp: wp_simp)

lemma wp_value: "P v \<turnstile> wp s E (Val v) P"
  by (auto simp: wp_simp fupd_intro upred_wand_holdsE)

lemma wp_fupd_helper: "\<forall>\<^sub>u v. (upred_emp ={E}=\<^emph> upred_emp)"
  apply (subst upred_holds_entails)
  apply (rule upred_forallI)
  using fupd_intro upred_holds_entails by auto
  
lemma wp_strong_mono: 
assumes "s1 \<le> s2" 
shows "\<forall>\<^sub>uE1 E2 e P Q. (\<upharpoonleft>(E1 \<subseteq> E2)) \<longrightarrow>\<^sub>u (wp s1 E1 e P -\<^emph> (\<forall>\<^sub>u v. (P v ={E2}=\<^emph> Q v)) -\<^emph> wp s2 E2 e Q)"
  (is "upred_holds ?goal")  
  apply (rule loebI)
  apply (auto intro!: upred_forallI upred_implI_pure upred_wandI)
  subgoal for E1 E2 e P Q
  apply (subst wp_simp[of _ E1])
  apply (subst wp_simp[of _ E2])
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
    using assms
    apply (cases s1; cases s2)
    by auto
  subgoal for v
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ v]])
    apply (rule upred_wandE)
    apply (rule upred_entails_trans[OF _ fupd_ext])
  by (auto intro!: upred_entails_trans[OF upred_weakeningR] upred_wand_holdsE[OF fupd_mask_mono])
  done
done

lemma fupd_wp: "\<Turnstile>{E}=> (wp s E e P) \<turnstile> wp s E e P"
  apply (subst wp_simp)
  apply (subst wp_simp[of s E e P])
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

lemma wp_fupd: "wp s E e (\<lambda>v. \<Turnstile>{E}=> P v) \<turnstile> wp s E e P"
  apply (rule add_holds[OF wp_strong_mono[of s s, simplified]])
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
assumes "(\<And>v. P v \<turnstile> Q v)"
shows "wp s E e P \<turnstile> wp s E e Q"
  apply (rule add_holds[OF wp_strong_mono[of s s, simplified]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ E]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ E]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ e]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ P]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ Q]])
  apply (auto intro!: upred_entails_substE[OF upred_entail_eqL[OF upred_emp_impl]]
    upred_entails_trans[OF upred_wand_apply])
  apply (rule add_holds[OF upred_holds_forall[OF fupd_intro'[OF assms, of _ E]], of _ id, simplified])
  apply (subst upred_sep_comm)
  by (rule upred_wand_apply)

lemma wp_atomic: "atomic (stuckness_to_atomicity s) e \<Longrightarrow>
  \<Turnstile>{E1,E2}=> wp s E2 e (\<lambda>v. \<Turnstile>{E2,E1}=> P v) \<turnstile> wp s E1 e P" sorry

lemma wp_bind: "wp s E e (\<lambda>v. wp s E (lang_ctxt K (of_val v)) P) \<turnstile> wp s E (lang_ctxt K e) P" sorry
lemma wp_bind': "wp s E e (\<lambda>v. wp s E (C (of_val v)) P) \<turnstile> wp s E (C e) P" sorry
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


lemma wp_pure': "\<lbrakk>pure_exec b n e1 e2; b; P \<turnstile> wp s E (fill K e2) Q\<rbrakk> \<Longrightarrow>
  P \<turnstile> wp s E (fill K e1) Q" sorry

lemma wp_pure: "\<lbrakk>pure_exec b n e1 e2; b; P \<turnstile> wp s E e2 Q\<rbrakk> \<Longrightarrow>
  P \<turnstile> wp s E e1 Q" by (rule wp_pure'[where K = "[]", unfolded fill_def, simplified])

lemma wp_let_bind: "Q \<turnstile> wp s E e (\<lambda>v. wp s E (let: x := (of_val v) in e2 endlet) P) \<Longrightarrow> 
  Q \<turnstile> wp s E (let: x := e in e2 endlet) P" sorry (* Would follow from wp_bind *)

lemma wp_let_bind': "Q \<turnstile> wp s E e (\<lambda>v. wp s E (let: x := C (of_val v) in e2 endlet) P) \<Longrightarrow> 
  Q \<turnstile> wp s E (let: x := C e in e2 endlet) P" sorry

lemma elim_modal_fupd_wp_atomic: "atomic (stuckness_to_atomicity s) e \<Longrightarrow> 
  elim_modal (\<Turnstile>{E1,E2}=>P) P (wp s E1 e Q) (wp s E2 e (\<lambda>v. \<Turnstile>{E2,E1}=> Q v))"
  unfolding elim_modal_def
  apply (entails_substL rule: upred_wand_holdsE[OF fupd_frame_r])
  apply (entails_substL rule: fupd_mono[OF upred_wand_apply])
  by (rule wp_atomic, assumption)

lemma wp_is_except_zero: "is_except_zero (wp s E e P)"
  unfolding is_except_zero_def
  apply (rule upred_entails_trans[OF _ fupd_wp])
  apply (rule upred_entails_trans[OF _ is_except_zero_fupd[unfolded is_except_zero_def]])
  by (auto intro: upred_entails_trans[OF _ except_zero_mono[OF upred_wand_holdsE[OF fupd_intro]]])

lemma wp_load: "P \<^emph> (l\<mapsto>{p}v) \<turnstile> Q v \<Longrightarrow> P \<^emph> (l\<mapsto>{p}v) \<turnstile> wp s E (Load #[l]) Q"
  sorry

lemma wp_pure_let: "\<lbrakk>pure_exec b n e1 (Val v); b; P \<turnstile> wp s E (subst' x v e2) Q\<rbrakk> \<Longrightarrow>
  P \<turnstile> wp s E (let: x := e1 in e2 endlet) Q"
  sorry

lemma wp_cmpxchg_fail: "\<lbrakk>v\<noteq>v1; vals_compare_safe v v1; P \<^emph> (l\<mapsto>{p}v) \<turnstile> wp s E (#[(v,False)]) Q\<rbrakk>
  \<Longrightarrow> P \<^emph> (l\<mapsto>{p}v) \<turnstile> wp s E (CmpXchg (Val #[l]) v1 v2) Q"
  sorry  
end
end   