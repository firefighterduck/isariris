theory WeakestPrecondition
imports "../IrisCore/Invariant" Notation LanguageDefs
begin        

named_theorems heap_inG_axiom
named_theorems proph_inG_axiom
named_theorems inv_inG_axiom

context
fixes get_inv :: "gname \<Rightarrow> 'res :: ucamera \<Rightarrow> inv option"
  and put_inv
  and get_heap :: "gname \<Rightarrow> 'res \<Rightarrow> heap_lang_heap option"
  and put_heap
  and get_prophm :: "gname \<Rightarrow> 'res \<Rightarrow> (proph_id, val\<times>val) proph_mapGS option"
  and put_prophm
assumes inv_inG: "inG get_inv put_inv"
  and heap_inG: "inG get_heap put_heap"
  and prophm_inG: "inG get_prophm put_prophm"
begin
  
abbreviation fancy_upd ("\<Turnstile>{_,_}=>_") where "fancy_upd \<equiv> ViewShift.fancy_upd put_inv"
abbreviation wand_fupd ("_={_,_}=\<^emph>_") where "wand_fupd \<equiv> ViewShift.wand_fupd put_inv"
abbreviation linear_fupd ("\<Turnstile>{_}=>_") where "linear_fupd \<equiv> ViewShift.linear_fupd put_inv"
abbreviation wand_linear_fupd ("_={_}=\<^emph>_") where "wand_linear_fupd \<equiv> ViewShift.wand_linear_fupd put_inv"
abbreviation fancy_step ("\<Turnstile>{_}[_]\<triangleright>=>_") where "fancy_step \<equiv> ViewShift.fancy_step put_inv"  
abbreviation fancy_wand_step ("_={_}[_]\<triangleright>=\<^emph>_") where "fancy_wand_step \<equiv> ViewShift.fancy_wand_step put_inv"  
abbreviation fancy_linear_wand_step ("_={_}\<triangleright>=\<^emph>_") where
  "fancy_linear_wand_step \<equiv> ViewShift.fancy_linear_wand_step put_inv"
abbreviation state_interp where "state_interp \<equiv> LanguageDefs.state_interp put_prophm put_heap"
abbreviation points_to where "points_to \<equiv> AuthHeap.points_to put_heap"
abbreviation points_to_disc where "points_to_disc \<equiv> AuthHeap.points_to_disc put_heap"
abbreviation points_to_own where "points_to_own \<equiv> AuthHeap.points_to_own put_heap"
abbreviation points_to_full where "points_to_full \<equiv> AuthHeap.points_to_full put_heap"

notation points_to ("_ \<mapsto>{_} _" 60)
notation points_to_disc (infix "\<mapsto>\<box>" 60)
notation points_to_own ("_\<mapsto>{#_}_" 60)
notation points_to_full (infix "\<mapsto>\<^sub>u" 60)
  
subsection \<open>Weakest Preconditions\<close>

lift_definition wp_pre :: "stuckness \<Rightarrow> ((mask \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f) -c>
  (mask \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f))" is
  "\<lambda>s wp_arg E e1 \<Phi>. (case HeapLang.to_val e1 of Some v \<Rightarrow> \<Turnstile>{E}=> (\<Phi> v)
    | None \<Rightarrow> (\<forall>\<^sub>u \<sigma>1 \<kappa> \<kappa>s.
      ((state_interp \<sigma>1 (\<kappa>@\<kappa>s)) ={E,Set.empty}=\<^emph>
        ((\<upharpoonleft>(case s of NotStuck \<Rightarrow> reducible e1 \<sigma>1 | _ \<Rightarrow> True)) \<^emph>
        (\<forall>\<^sub>u e2 \<sigma>2 efs. ((\<upharpoonleft>(prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs))
          ={Set.empty}\<triangleright>=\<^emph> (\<Turnstile>{Set.empty,E}=> ((state_interp \<sigma>2 \<kappa>s) \<^emph>
            (wp_arg E e2 \<Phi>) \<^emph> ([\<^emph>\<^sub>l:] efs (\<lambda>ef. wp_arg UNIV ef (\<lambda>_. upred_emp)))))))))))"
apply (auto simp: contractive_alt_def contr_contr_alt n_equiv_fun_def split: option.splits nat.splits)
apply (auto simp: ofe_refl less_Suc_eq_le ofe_mono intro!: upred_ne_rule contractiveE[OF upred_later_contr])
apply (simp_all add: n_equiv_fun_def ofe_mono)
using inv_inG by simp_all

definition wp :: "stuckness \<Rightarrow> mask \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" where
  "wp s \<equiv> fixpoint (wp_pre s)"

lemma wp_unfold: "wp s E e P \<stileturn>\<turnstile> Rep_contr (wp_pre s) (wp s) E e P"
  unfolding wp_def using upred_eq_entails fixpoint_unfold[of "wp_pre s", unfolded ofe_eq_fun_def]
  by blast

abbreviation WP :: "expr \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" ("WP _ {{ _ }}") where
  "WP e {{ \<Phi> }} \<equiv> wp NotStuck UNIV e \<Phi>"

abbreviation hoare :: "'res upred_f \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> bool" ("{{ _ }} _ {{ _ }}") where
  "{{ P }} e {{ \<Phi> }} \<equiv> P \<turnstile> WP e {{ \<Phi> }}"

abbreviation texan :: "'res upred_f \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" ("{{{ _ }}} _ {{{ _ }}}") where
  "{{{ P }}} e {{{ Q }}} \<equiv> \<box>(\<forall>\<^sub>u \<Phi>. P -\<^emph> (\<triangleright>(\<forall>\<^sub>u v. Q v -\<^emph> \<Phi> v)) -\<^emph> WP e {{ \<Phi> }})"

abbreviation texan2 :: "'res upred_f \<Rightarrow> expr \<Rightarrow> stuckness \<Rightarrow> mask \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" 
  ("{{{ _ }}} _ @ _ ; _ {{{ _ }}}") where
  "{{{ P }}} e @ s; E {{{ Q }}} \<equiv> \<box>(\<forall>\<^sub>u \<Phi>. P -\<^emph> (\<triangleright>(\<forall>\<^sub>u v. Q v -\<^emph> \<Phi> v)) -\<^emph> wp s E e \<Phi>)"

lemma texan_to_wp: "{{{ P }}} e @ s; E {{{ Q }}} \<turnstile> (P -\<^emph> wp s E e Q)"
apply (rule upred_entails_trans[OF upred_persisE])
apply (rule upred_entails_trans[OF upred_forall_inst[of _ Q]])
apply (rule upred_wandI)
apply (iApply rule: upred_wand_apply)
by (rule upred_true_wand)

lemma "{{{ P }}} e {{{ Q }}} \<Longrightarrow> {{ P }} e {{ Q }}"
  apply (rule upred_wand_holdsE[unfolded upred_holds_entails])
  unfolding upred_holds_entails using texan_to_wp upred_entails_trans by blast

text \<open>
  First we show that some basic properties of wp hold for inputs in the domain, then we 
  always assume that all values lie in the domain.
\<close>

lemma wp_value_fupd: "wp s E (of_val v) P \<stileturn>\<turnstile> \<Turnstile>{E}=> P v"
  apply (rule upred_entail_eq_trans[OF wp_unfold])
  by (simp add: wp_pre.rep_eq)

lemma wp_value: "P v \<turnstile> wp s E (Val v) P"
  apply (rule upred_entails_trans[OF _ upred_entail_eqR[OF wp_unfold]])
  by (auto simp: wp_pre.rep_eq fupd_intro[OF inv_inG] upred_wand_holdsE)

lemma wp_fupd_helper: "\<forall>\<^sub>u v. (upred_emp ={E}=\<^emph> upred_emp)"
  apply (subst upred_holds_entails)
  apply (rule upred_forallI)
  using fupd_intro[OF inv_inG] upred_holds_entails by auto
  
lemma wp_strong_mono: 
assumes "s1 \<le> s2" 
shows "\<forall>\<^sub>uE1 E2 e P Q. (\<upharpoonleft>(E1 \<subseteq> E2)) \<longrightarrow>\<^sub>u (wp s1 E1 e P -\<^emph> (\<forall>\<^sub>u v. (P v ={E2}=\<^emph> Q v)) -\<^emph> wp s2 E2 e Q)"
  (is "upred_holds ?goal")
  apply (rule loebI)
  apply (auto intro!: upred_forallI upred_implI_pure upred_wandI)
  subgoal for E1 E2 e P Q
  apply (rule upred_entails_trans[OF _ upred_entail_eqR[OF wp_unfold]])
  apply (move_sepL "wp s1 E1 e P")
  apply (rule upred_entails_substE[OF upred_entail_eqL[OF wp_unfold]])
  unfolding wp_pre.rep_eq
  apply (cases "HeapLang.to_val e")
  apply auto
  apply (auto intro!: upred_forallI upred_wandI)
    subgoal for \<sigma>1 \<kappa> \<kappa>s
    apply (rule add_holds[OF fupd_mask_subseteq[OF inv_inG]], assumption)
    apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of E2 E1]])
    apply (rule fupd_frame_mono[OF inv_inG])
    apply (move_sepL "\<forall>\<^sub>u (x::state). ?P x")
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<sigma>1]])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<kappa>]])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<kappa>s]])
    apply iApply_wand
    apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of E1 "{}"]])
    apply (rule fupd_frame_mono[OF inv_inG])
    apply (simp add: upred_sep_assoc_eq)
    apply (rule upred_entails_trans[OF upred_sep_comm2R])
    apply (rule upred_pure_impl)
    apply (rule upred_entails_trans[OF _ fupd_empty[OF inv_inG]])
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
      apply (rule fupd_frame_mono[OF inv_inG])
      apply (rule upred_entails_trans[OF upred_sep_comm3L])
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], unfolded upred_sep_assoc_eq])
      apply (rule upred_later_mono_extR)
      apply (simp add: upred_sep_assoc_eq)
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_trans[OF upred_sep_comm3L])
      apply (rule fupd_frame_mono[OF inv_inG])
      apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of "{}" E1]])
      apply (rule fupd_frame_mono[OF inv_inG])
      apply (simp add: upred_sep_assoc_eq)
      apply (rule upred_entails_trans[OF _ fupd_mono[OF inv_inG upred_entails_eq[OF upred_sep_comm2L]]])
      apply (rule upred_entails_trans[OF _ fupd_mono[OF inv_inG upred_sep_comm2R]])
      apply (rule upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_frame_r[OF inv_inG]]])
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_trans[OF upred_sep_comm2R])
      apply (rule upred_frame)
      apply (rule upred_entails_trans[OF upred_sep_comm3M])
      apply (rule upred_entails_trans[OF upred_sep_comm2R])
      apply (auto simp: upred_true_sep intro!: fupd_frame_mono[OF inv_inG])
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
    apply (iForallL v)
    apply (rule upred_wandE)
    apply (rule upred_entails_trans[OF _ fupd_ext[OF inv_inG]])
  by (auto intro!: upred_entails_trans[OF upred_weakeningR] upred_wand_holdsE[OF fupd_mask_mono[OF inv_inG]])
  done
done

lemma wp_strong_monoI: "\<lbrakk>s1 \<le> s2; E1 \<subseteq> E2\<rbrakk> \<Longrightarrow> wp s1 E1 e P \<turnstile> ((\<forall>\<^sub>u v. ((P v) ={E2}=\<^emph> Q v)) -\<^emph> wp s2 E2 e Q)"
proof - 
assume assms: "s1 \<le> s2" "E1 \<subseteq> E2"
from wp_strong_mono[OF assms(1), to_entailment] have
  "upred_emp \<turnstile> ((\<upharpoonleft>(E1 \<subseteq> E2)) \<longrightarrow>\<^sub>u (wp s1 E1 e P -\<^emph> (\<forall>\<^sub>uv. ((P v)={E2,E2}=\<^emph>Q v)) -\<^emph> wp s2 E2 e Q))"
  by (auto dest!: upred_entails_trans[OF _ upred_forall_inst])
with assms(2) show ?thesis 
by (smt (verit, best) add_holds entails_impl_true upred_holds_entails upred_wand_apply)
qed

lemma fupd_wp: "\<Turnstile>{E}=> (wp s E e P) \<turnstile> wp s E e P"
  apply (rule upred_entails_trans[OF _ upred_entail_eqR[OF wp_unfold]])
  apply(rule upred_entails_trans[OF fupd_mono[OF inv_inG upred_entail_eqL[OF wp_unfold]]])
  unfolding wp_pre.rep_eq
  apply (cases "HeapLang.to_val e")
  apply auto
  apply (auto intro!: upred_forallI)
  subgoal for \<sigma>1 \<kappa> \<kappa>s
    apply (rule upred_wandI)
    apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of E E]])
    apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
    apply (rule fupd_frame_mono[OF inv_inG])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<sigma>1]])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<kappa>]])
    apply (rule upred_entails_substE[OF upred_forall_inst[of _ \<kappa>s]])
    by (auto intro: upred_entails_trans[OF upred_wand_apply])
  by (simp add: fupd_mask_trans[OF inv_inG])

lemma wp_fupd: "wp s E e (\<lambda>v. \<Turnstile>{E}=> P v) \<turnstile> wp s E e P"
  apply (rule add_holds[OF wp_strong_mono[of s s, simplified]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ E]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ E]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ e]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ "(\<lambda>v. \<Turnstile>{E}=> P v)"]])
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ P]])
  apply (auto intro!: upred_entails_substE[OF upred_entail_eqL[OF upred_emp_impl]]
    upred_entails_trans[OF upred_wand_apply])
  apply (simp add: emp_rule)
  by (rule upred_true_wand) 
  
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
  apply (rule add_holds[OF upred_holds_forall[OF fupd_intro'[OF inv_inG assms, of _ E]], of _ id, simplified])
  apply (subst upred_sep_comm)
  by (rule upred_wand_apply)

lemma wp_mono':
assumes "(\<And>v. P v \<turnstile> Q v)"
shows "R \<^emph> wp s E e P \<turnstile> wp s E e Q"
  using wp_mono[OF assms] assms upred_entails_trans upred_weakeningR wp_mono 
  by blast

lemma wp_atomic: 
assumes "atomic (stuckness_to_atomicity s) e"
shows "\<Turnstile>{E1,E2}=> wp s E2 e (\<lambda>v. \<Turnstile>{E2,E1}=> P v) \<turnstile> wp s E1 e P"
  apply (rule upred_entails_trans[OF _ upred_entail_eqR[OF wp_unfold]])
  apply (rule upred_entails_trans[OF fupd_mono[OF inv_inG upred_entail_eqL[OF wp_unfold]]])
  unfolding wp_pre.rep_eq
  apply (cases "HeapLang.to_val e")
  apply simp_all
  prefer 2 apply (rule upred_entails_trans[OF fupd_mask_trans[OF inv_inG]])+ apply simp
  apply iForallR+
  apply (rule upred_wandI)
  apply (check_moveL "\<Turnstile>{?E1,?E2}=>?P", rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])
  subgoal for \<sigma>1 \<kappa> \<kappa>s apply (iForallL \<sigma>1, iForallL \<kappa>,iForallL \<kappa>s)
  apply iApply_wand
  apply (rule fupd_mono[OF inv_inG])
  apply iPureL
  apply iForallR+ subgoal for e2 \<sigma>2 efs apply (iForallL e2, iForallL \<sigma>2, iForallL efs)
  apply (rule upred_wandI, iPureL)
  apply (iApply_step "?P" rule: step_fupdN_wand[OF inv_inG, of 1 "{}" "{}"])
  apply (rule upred_entails_trans[OF upred_true_wand])
  apply (rule framing_emp, frame_solver, iris_simp, rule upred_wandI, iris_simp, rule upred_entails_refl)
  apply (rule fupd_mono[OF inv_inG], rule upred_later_mono, rule fupd_mono[OF inv_inG])
  apply (rule elim_modal_entails[OF elim_modal_fupd[OF inv_inG]])
  apply (cases s, auto)
    subgoal
    apply (iApply rule: upred_entail_eqL[OF wp_unfold])
    apply (entails_substR rule: fupd_mono[OF inv_inG upred_sep_mono[OF upred_entails_refl 
        upred_sep_mono[OF upred_entail_eqR[OF wp_unfold] upred_entails_refl]], unfolded upred_sep_assoc_eq])
    unfolding wp_pre.rep_eq
    apply (cases "HeapLang.to_val e2", auto)
    prefer 2 
    apply (check_moveL "\<Turnstile>{?E1,?E2}=>?P")
    apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]])+
    apply (rule upred_entails_trans[OF _ fupd_intro[OF inv_inG, to_entailment]])
    apply (rule framing, log_prog_solver log_prog_rule: inv_inG)+
    apply (rule framing_emp, log_prog_solver)
    apply iris_simp
    apply (rule upred_entails_trans[OF _ fupd_intro[OF inv_inG, to_entailment]])
    apply iris_simp
    apply (iForallL \<sigma>2, iForallL "[]::observation list",iForallL \<kappa>s)
    apply iApply_wand
    apply (check_moveL "\<Turnstile>{?E1,?E2}=>?P", rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]], iris_simp)
    apply (rule upred_entails_trans[OF upred_weakeningL])
    apply (subst reducible_def)
    apply iPureL using atomicE[OF assms, of \<sigma>1 \<kappa> e2 \<sigma>2 efs] 
    by (auto simp: stuckness_to_atomicity_def irreducible_def)
  using atomicE[OF assms, of \<sigma>1 \<kappa> e2 \<sigma>2 efs]
  apply (auto simp: stuckness_to_atomicity_def dest!: to_val_cases)
  apply (iApply rule: upred_entail_eqL[OF wp_value_fupd])
  apply (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG]], rule fupd_frame_mono[OF inv_inG])
  apply (move_sepR "wp ?m ?E ?e ?p", entails_substR rule: wp_value)
  by iris_simp
  done done

lemma wp_bind: "wp s E e (\<lambda>v. wp s E (lang_ctxt K (of_val v)) P) \<turnstile> wp s E (lang_ctxt K e) P" sorry
lemma wp_bind': "wp s E e (\<lambda>v. wp s E (C (of_val v)) P) \<turnstile> wp s E (C e) P" sorry
lemma wp_bind_inv: "wp s E (lang_ctxt K e) P \<turnstile> wp s E e (\<lambda>v. wp s E (lang_ctxt K (of_val v)) P)" sorry
lemma wp_stuck_mono: 
  assumes "s1 \<le> s2"
  shows "wp s1 E e P \<turnstile> wp s2 E e P"
  apply (entails_substL rule: wp_strong_monoI[OF assms subset_refl, where ?Q = P])
  apply (entails_substL rule: upred_entails_trans[OF upred_wandL[OF upred_forall_mono[OF 
      fupd_intro[OF inv_inG, simplified upred_holds_entails]]]])
  apply iris_simp
  by (rule upred_true_wand)

lemma wp_stuck_weaken: "wp s E e P \<turnstile> wp MaybeStuck E e P" using wp_stuck_mono[of s MaybeStuck] by simp
lemma wp_frame_simp: "wp s E e (\<lambda>v. Q v) \<^emph> P \<turnstile> wp s E e (\<lambda>v. Q v \<^emph> P)" sorry

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

lemma wp_pure_step_later: "\<lbrakk>pure_exec b n e1 e2; b\<rbrakk> \<Longrightarrow>
  (upred_later^^n) (wp s E e2 \<Phi>) \<turnstile> wp s E e1 \<Phi>"
sorry
  
lemma wp_let_bind: "Q \<turnstile> wp s E e (\<lambda>v. wp s E (let: x := (of_val v) in e2 endlet) P) \<Longrightarrow> 
  Q \<turnstile> wp s E (let: x := e in e2 endlet) P" sorry (* Would follow from wp_bind *)

lemma wp_let_bind': "Q \<turnstile> wp s E e (\<lambda>v. wp s E (let: x := C (of_val v) in e2 endlet) P) \<Longrightarrow> 
  Q \<turnstile> wp s E (let: x := C e in e2 endlet) P" sorry

lemma elim_modal_fupd_wp_atomic: "atomic (stuckness_to_atomicity s) e \<Longrightarrow> 
  elim_modal (\<Turnstile>{E1,E2}=>P) P (wp s E1 e Q) (wp s E2 e (\<lambda>v. \<Turnstile>{E2,E1}=> Q v))"
  unfolding elim_modal_def
  apply (entails_substL rule: upred_wand_holdsE[OF fupd_frame_r[OF inv_inG]])
  apply (entails_substL rule: fupd_mono[OF inv_inG upred_wand_apply])
  by (rule wp_atomic, assumption)

lemma wp_is_except_zero [iez_rule,log_prog_rule]: "is_except_zero (wp s E e P)"
  unfolding is_except_zero_def
  apply (rule upred_entails_trans[OF _ fupd_wp])
  apply (rule upred_entails_trans[OF _ is_except_zero_fupd[OF inv_inG, unfolded is_except_zero_def]])
  by (auto intro: upred_entails_trans[OF _ except_zero_mono[OF upred_wand_holdsE[OF fupd_intro[OF inv_inG]]]])

lemma wp_load: "P \<^emph> (l\<mapsto>{p}v) \<turnstile> Q v \<Longrightarrow> P \<^emph> (l\<mapsto>{p}v) \<turnstile> wp s E (Load #[l]) Q"
  sorry

lemma wp_pure_let: "\<lbrakk>pure_exec b n e1 (Val v); b; P \<turnstile> wp s E (subst' x v e2) Q\<rbrakk> \<Longrightarrow>
  P \<turnstile> wp s E (let: x := e1 in e2 endlet) Q"
  sorry

lemma wp_cmpxchg_fail: "\<lbrakk>v\<noteq>v1; vals_compare_safe v v1; P \<^emph> (l\<mapsto>{p}v) \<turnstile> wp s E (#[(v,False)]) Q\<rbrakk>
  \<Longrightarrow> P \<^emph> (l\<mapsto>{p}v) \<turnstile> wp s E (CmpXchg (Val #[l]) v1 v2) Q"
  sorry   

lemma wp_cmpxchg_success: "\<lbrakk>v=v1; vals_compare_safe v v1; P \<^emph> (l\<mapsto>{p}v2) \<turnstile> wp s E (#[(v,True)]) Q\<rbrakk>
  \<Longrightarrow> P \<^emph> (l\<mapsto>{p}v) \<turnstile> wp s E (CmpXchg (Val #[l]) v1 v2) Q"
  sorry

lemma wp_alloc: "wp s E (Alloc (Val v)) (\<lambda>lv. (\<exists>\<^sub>u l. ((\<upharpoonleft>(lv=#[l])) \<^emph> (l\<mapsto>\<^sub>uv))))"
sorry

lemma wp_alloc': "(\<And>l. P\<^emph>(l\<mapsto>\<^sub>uv) \<turnstile> wp s E #[l] \<Phi>) \<Longrightarrow> P \<turnstile> wp s E (Alloc (Val v)) \<Phi>"
sorry

lemma wp_store_texan: "{{{ \<triangleright>(l\<mapsto>\<^sub>uv') }}} #[l] \<leftarrow> (Val v) @ s; E {{{ \<lambda>_. l\<mapsto>\<^sub>u v }}}"
sorry

lemma wp_store: "\<triangleright>(l\<mapsto>\<^sub>uv') \<turnstile> wp s E (Store #[l] v) (\<lambda>_. l\<mapsto>\<^sub>uv)"
  by (rule upred_wandE[OF upred_entails_trans[OF wp_store_texan[to_entailment] texan_to_wp], unfolded emp_rule])
 
lemma wp_store': 
  assumes "P\<^emph>(l\<mapsto>\<^sub>uv) \<turnstile> \<triangleright>wp s E (#[()]) \<Phi>" 
  shows "P\<^emph>(l\<mapsto>\<^sub>uv') \<turnstile> wp s E (Store #[l] v) \<Phi>"
proof -
  have aux: "((\<upharpoonleft>(\<kappa>=[]))-\<^emph> Q UnitE (state_upd_heap (fmupd l (Some v)) \<sigma>1) []) \<turnstile>
    (\<forall>\<^sub>ue2 \<sigma>2 efs. ((\<upharpoonleft>(\<kappa> = [] \<and> e2 = UnitE \<and> \<sigma>2 = state_upd_heap (fmupd l (Some v)) \<sigma>1 \<and> efs = [])) -\<^emph> (Q e2 \<sigma>2 efs)))"
    for \<kappa> Q \<sigma>1 apply iForallR+ apply (rule upred_wandI) apply iPureL by (simp add: upred_true_wand)  
  have aux2: "Q \<turnstile> R \<^emph> S \<Longrightarrow> Q \<turnstile> R \<^emph> \<Turnstile>{E,{}}=>\<Turnstile>{{},E}=>S" for Q R S :: "'res upred_f"
    by (meson empty_subsetI fupd_mask_intro_subseteq[OF inv_inG] upred_entails_substI)
  have aux3: "\<Rrightarrow>\<^sub>b (heap_interp put_heap (heap (state_upd_heap (fmupd l (Some v)) \<sigma>1)) \<^emph> (l\<mapsto>\<^sub>uv))" for \<sigma>1
    unfolding upred_holds_entails heap_interp_def[OF heap_inG] points_to_def[OF heap_inG]
    own_heap_auth_def[OF heap_inG]
    apply (rule upred_entails_trans[OF _ upd_mono[OF upred_entail_eqL[OF inG.own_op[OF heap_inG]]]])
    apply (rule inG.own_alloc[OF heap_inG, to_entailment])
    by (auto simp: valid_def constr_heap_def prod_n_valid_def \<epsilon>_n_valid map_view_auth_def map_view_frag_def 
      view_both_valid map_view_rel_def valid_dfrac_own[unfolded valid_def] d_equiv state_upd_heap_def
      op_prod_def \<epsilon>_left_id)
  show ?thesis
  apply (entails_substR rule: upred_entail_eqR[OF wp_unfold])
  apply (auto simp: wp_pre.rep_eq)
  apply iForallR+
  apply (rule upred_wandI)
  unfolding state_interp_def[OF prophm_inG heap_inG]
  apply (iApply rule: points_to_lookup[OF heap_inG])
  apply iPureL
  apply (frule store_red[where ?v=v])
  apply (cases s, auto, iris_simp)
  subgoal for \<sigma>1 \<kappa> \<kappa>s
    unfolding prim_step_store apply simp
    apply (entails_substR rule: fupd_mono[OF inv_inG aux])
    apply (cases "\<kappa>=[]", iris_simp iris_simp: state_upd_proph)
    prefer 2
    apply (metis (no_types, opaque_lifting) add_holds empty_subsetI fupd_mask_subseteq inv_inG fupd_mono upred_emp_entailed upred_entails_trans upred_true_sep')
    apply (entails_substR rule: fupd_mono[OF inv_inG upred_true_wand'])
    apply (rule add_holds[OF aux3])
    apply (check_moveL "\<Rrightarrow>\<^sub>b ?P", rule elim_modal_entails'[OF elim_modal_upd[OF inv_inG]])
    apply (rule upred_entails_trans[OF _ fupd_mono[OF inv_inG fupd_intro[OF inv_inG, to_entailment]]])
    apply (rule upred_entails_trans[OF _ frameE[where ?Q = "\<triangleright>wp NotStuck E UnitE \<Phi>"]])
    prefer 2
    apply (rule fupd_frameR[OF inv_inG])+ apply (rule frame_later) 
    apply (rule fupd_frameR[OF inv_inG])+ apply (rule frame_rev, rule frame_refl)
    apply (rule upred_entails_substI[OF fupd_mono[OF inv_inG fupd_intro[OF inv_inG, to_entailment]]])
    apply (rule aux2)
    apply (move_sepR "\<triangleright>?p")
    apply (move_sepR "proph_map_interp ?put \<kappa>s ?p")
    apply iFrame_single
    apply (iDrop "heap_interp ?put (heap \<sigma>1)")
    apply (iDrop "l\<mapsto>\<^sub>uv'")
    apply (iApply rule: assms)
    by iFrame_single+
  subgoal for \<sigma>1 \<kappa> \<kappa>s
  unfolding prim_step_store apply simp
  apply (entails_substR rule: fupd_mono[OF inv_inG aux])
  apply (cases "\<kappa>=[]", iris_simp iris_simp: state_upd_proph)
  prefer 2
  apply (metis (no_types, opaque_lifting) inv_inG add_holds empty_subsetI fupd_mask_subseteq fupd_mono upred_emp_entailed upred_entails_trans upred_true_sep')
  apply (entails_substR rule: fupd_mono[OF inv_inG upred_true_wand'])
  apply (rule add_holds[OF aux3])
  apply (check_moveL "\<Rrightarrow>\<^sub>b ?P", rule elim_modal_entails'[OF elim_modal_upd[OF inv_inG]])
  apply (rule upred_entails_trans[OF _ fupd_mono[OF inv_inG fupd_intro[OF inv_inG, to_entailment]]])
  apply (rule upred_entails_trans[OF _ frameE[where ?Q = "\<triangleright>wp MaybeStuck E UnitE \<Phi>"]])
  prefer 2
  apply (rule fupd_frameR[OF inv_inG])+ apply (rule frame_later) 
  apply (rule fupd_frameR[OF inv_inG])+ apply (rule frame_rev, rule frame_refl)
  apply (rule upred_entails_substI[OF fupd_mono[OF inv_inG fupd_intro[OF inv_inG, to_entailment]]])
  apply (rule aux2)
  apply (move_sepR "\<triangleright>?p")
  apply (move_sepR "proph_map_interp ?put \<kappa>s ?p")
  apply iFrame_single
  apply (iDrop "heap_interp ?put (heap \<sigma>1)")
  apply (iDrop "l\<mapsto>\<^sub>uv'")
  apply (iApply rule: assms)
  by iFrame_single+
  done
qed

lemma wp_frame': "(\<And>x. can_be_split (Q x) (Q' x) P) \<Longrightarrow> (wp s E e Q') \<^emph> P \<turnstile> wp s E e Q"
sorry  

lemma wp_frame [frame_rule,log_prog_rule]: "(\<And>x. frame (P x) (Q x) R) \<Longrightarrow> frame (wp s E e P) (wp s E e Q) R"
  unfolding frame_def by (smt (verit) upred_entails_trans wp_frame_simp wp_mono)
end
  
text \<open>Because fupds often appear with schematic variables which make matching difficult, we just
  try the different elimination methods.\<close>

method fupd_elimL =
  check_moveL "fancy_upd ?p ?E1 ?E2 ?P",
    (rule elim_modal_entails'[OF elim_modal_fupd[OF inv_inG_axiom]]
    | rule fupd_mono[OF inv_inG_axiom] | rule elim_modal_entails[OF elim_modal_fupd[OF inv_inG_axiom]]
    | (rule elim_modal_entails[OF elim_modal_fupd_wp_atomic[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom]], 
        log_prog_solver)
    | (rule elim_modal_entails'[OF elim_modal_fupd_wp_atomic[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom]], 
        log_prog_solver));
  iris_simp

method iMod uses rule = iMod_raw fupd_elimL rule: rule
method iMod_wand for lhs_pat pat :: "'a::ucamera upred_f" = 
  iMod_raw_wand lhs_pat pat later_elim fupd_elimL
method iMod_step for pat :: "'a::ucamera upred_f" uses rule = 
  iMod_raw_step pat later_elim fupd_elimL rule: rule
  
method lift_modL for trm :: "'res::ucamera upred_f" methods m =
  match (trm) in "fancy_upd _ _ _ P" for P :: "'res upred_f" \<Rightarrow> 
    \<open>apply_prefer \<open>entails_substL rule: fupd_mono[OF inv_inG_axiom]\<close>, lift_modL P m\<close>
  \<bar> "wp _ _ _ _ _ _ (\<lambda>x. Q x)" for Q :: "val \<Rightarrow> 'res upred_f" \<Rightarrow> 
    \<open>apply_prefer \<open>entails_substL rule: wp_mono\<close>, lift_modL "Q v" m\<close>
  \<bar> "_" \<Rightarrow> \<open>rule upred_entails_trans, m, (rule upred_entails_refl)?\<close>

method lift_splitL for pat :: "'res::ucamera upred_f" =
  match conclusion in "hyps\<turnstile>_" for hyps :: "'res upred_f" \<Rightarrow>
    \<open>lift_modL hyps \<open>rule upred_entail_eqL[OF can_be_splitE], split_pat pat\<close>\<close>,
  (check_not_headL upred_emp) (* If splitting has not found any of the terms in the pattern*)
  
method lift_frame for pat :: "'res::ucamera upred_f" =
 rule upred_entails_trans[OF _ frameE], apply_first \<open>split_pat pat\<close>
   
method iFrame for pat :: "'res::ucamera upred_f" = 
  iris_simp, lift_splitL pat, lift_frame pat, iris_simp, move_sep_all_both pat,
  (rule upred_frame upred_emp_left | rule upred_entails_refl | rule upred_weakeningR)+, iris_simp

method frame_single =
  rule upred_entails_refl | rule upred_weakeningR | rule upred_weakeningL
| (rule framing, log_prog_solver)
| (rule framing_emp, log_prog_solver)

method frame_logic_programming for pat :: "'res::ucamera upred_f" =
  match (pat) in "rest\<^emph>_" for rest :: "'res upred_f" \<Rightarrow> \<open>frame_single, (frame_logic_programming rest)?\<close>
  \<bar> _ \<Rightarrow> \<open>frame_single\<close>
    
method iFrame2 for pat :: "'res::ucamera upred_f" =
  iris_simp, split_move pat, frame_logic_programming pat, iris_simp

method iFrame3 for pat :: "'res::ucamera upred_f" =
  iris_simp, split_move_ord pat, frame_logic_programming pat, iris_simp

method iWP uses rule = iris_simp,
  ((entails_substR rule: fupd_intro[OF inv_inG_axiom] | entails_substR rule: upred_laterI 
    | entails_substR rule: except_zeroI | entails_substR rule: updI)+)?,
  iApply rule: rule[OF inv_inG_axiom heap_inG_axiom proph_inG_axiom, simplified], iris_simp
end