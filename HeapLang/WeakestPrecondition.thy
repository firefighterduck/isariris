theory WeakestPrecondition
imports "../IrisCore/Invariant" "../IrisCore/AuthHeap" HeapLang State PrimitiveLaws Notation
begin

subsection \<open>Weakest Preconditions\<close>

definition state_interp :: "state \<Rightarrow> observation list \<Rightarrow> iprop" where
  "state_interp \<sigma> \<kappa>s = heap_interp (heap \<sigma>) \<^emph> proph_map_interp \<kappa>s (used_proph_id \<sigma>)"

datatype stuckness = NotStuck | MaybeStuck
instantiation stuckness :: ord begin
fun less_eq_stuckness :: "stuckness \<Rightarrow> stuckness \<Rightarrow> bool" where
  "less_eq_stuckness MaybeStuck NotStuck = False"
| "less_eq_stuckness _ _ = True"
fun less_stuckness :: "stuckness \<Rightarrow> stuckness \<Rightarrow> bool" where
  "less_stuckness MaybeStuck NotStuck = False"
| "less_stuckness MaybeStuck MaybeStuck = False"
| "less_stuckness NotStuck NotStuck = False"
| "less_stuckness _ _ = True"
instance ..
end

definition fill :: "ectx_item list \<Rightarrow> expr \<Rightarrow> expr"  where "fill K e =  fold fill_item K e"

definition prim_step :: "expr \<Rightarrow> state \<Rightarrow> observation list \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> bool" where
  "prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs \<equiv> \<exists>K e1' e2'. ((e1=fill K e1') \<and> (e2=fill K e2') \<and> head_step e1' \<sigma>1 \<kappa> e2' \<sigma>2 efs)"

function wp :: "stuckness \<Rightarrow> mask \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> iprop) \<Rightarrow> iprop" where
  "wp s E e1 \<Phi> = (case HeapLang.to_val e1 of Some v \<Rightarrow> \<Turnstile>{E}=> (\<Phi> v)
    | None \<Rightarrow> (\<forall>\<^sub>u \<sigma>1 \<kappa> \<kappa>s.
      ((state_interp \<sigma>1 (\<kappa>@\<kappa>s)) ={E,Set.empty}=\<^emph>
        ((\<upharpoonleft>(case s of NotStuck \<Rightarrow> red e1 \<sigma>1 | _ \<Rightarrow> True)) \<^emph>
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
  
lemma wp_lift_step_fupdN: 
assumes "HeapLang.to_val e1 = None"
shows "(\<forall>\<^sub>u \<sigma>1 \<kappa> \<kappa>s. ((state_interp \<sigma>1 (\<kappa>@\<kappa>s)) ={E,Set.empty}=\<^emph>
  ((\<upharpoonleft>(case s of NotStuck \<Rightarrow> red e1 \<sigma>1 | _ \<Rightarrow> True)) \<^emph>
  (\<forall>\<^sub>u e2 \<sigma>2 efs. ((\<upharpoonleft>(prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs)) ={Set.empty}\<triangleright>=\<^emph> 
    (\<Turnstile>{Set.empty,E}=> ((state_interp \<sigma>2 \<kappa>s) \<^emph>
      (wp s E e2 \<Phi>) \<^emph> ([\<^emph>\<^sub>l:] efs (\<lambda>ef. wp s UNIV ef (\<lambda>_. upred_emp))))))))))
   \<turnstile> wp s E e1 \<Phi>"
 sorry (* Axiomatized as reasoning with wp_dom is quite hard.*)
end   
end