theory ParSpec
imports "../HeapLang/Par" "../HeapLang/WeakestPrecondition" "../SpinLock/BruteForceAutomation"
begin

type_synonym spawn_token = "unit ex"

context 
fixes get_spawn :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> spawn_token option"
  and put_spawn
  and get_heap :: "gname \<Rightarrow> 'res \<Rightarrow> heap_lang_heap option"
  and put_heap
  and get_inv :: "gname \<Rightarrow> 'res \<Rightarrow> inv option"
  and put_inv
  and get_proph :: "gname \<Rightarrow> 'res \<Rightarrow> (proph_id, val\<times>val) proph_mapGS option"
  and put_proph
  and spawn_name :: namespace
assumes spawn_inG: "inG get_spawn put_spawn"
  and inv_inG[inv_inG_axiom]: "inG get_inv put_inv"
  and heap_inG[heap_inG_axiom]: "inG get_heap put_heap"
  and prophm_inG[proph_inG_axiom]: "inG get_proph put_proph"
begin

lemmas wp_inG = inv_inG heap_inG prophm_inG

abbreviation points_to_own' ("_\<mapsto>{#_}_" 60) where "points_to_own' \<equiv> AuthHeap.points_to_own put_heap"
abbreviation points_to_full' (infix "\<mapsto>\<^sub>u" 60) where "points_to_full' \<equiv> AuthHeap.points_to_full put_heap"
abbreviation inv where "inv \<equiv> Invariant.inv put_inv"
abbreviation WP' ("WP _ {{ _ }}") where "WP e {{ Q }} \<equiv> WeakestPrecondition.WP put_inv put_heap put_proph e Q"
abbreviation wand_linear_fupd' ("_={_}=\<^emph>_") where "wand_linear_fupd' \<equiv> ViewShift.wand_linear_fupd put_inv"
abbreviation linear_fupd' ("\<Turnstile>{_}=>_") where "linear_fupd' \<equiv> ViewShift.linear_fupd put_inv"
abbreviation texan' ("{{{ _ }}} _ {{{ _ }}}") where "texan' \<equiv> WeakestPrecondition.texan put_inv put_heap put_proph"
abbreviation fancy_upd' ("\<Turnstile>{_,_}=>_") where "fancy_upd' \<equiv> ViewShift.fancy_upd put_inv"
abbreviation wand_fupd' ("_={_,_}=\<^emph>_") where "wand_fupd' \<equiv> ViewShift.wand_fupd put_inv"

definition spawn_inv :: "gname \<Rightarrow> loc \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" where
  "spawn_inv \<gamma> l \<Psi> \<equiv> \<exists>\<^sub>u lv. (l\<mapsto>\<^sub>ulv) \<^emph> ((\<upharpoonleft>(lv=NoneV)) \<or>\<^sub>u (\<exists>\<^sub>u w. (\<upharpoonleft>(lv=SomeV w)) 
    \<^emph> (\<Psi> w \<or>\<^sub>u own put_spawn \<gamma> (Ex ()))))"

definition join_handle :: "loc \<Rightarrow> (val \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" where
  "join_handle l \<Psi> \<equiv> \<exists>\<^sub>u \<gamma>. ((own put_spawn \<gamma> (Ex ())) \<^emph> inv spawn_name (spawn_inv \<gamma> l \<Psi>))"

lemma spawn_token_alloc[alloc_rule]: "\<exists>\<^sub>u \<gamma>.\<Rrightarrow>\<^sub>b (own put_spawn \<gamma> (Ex ()))"
  apply iIntro
  apply (iExistsR "0::nat")
  apply (entails_substR rule: inG.own_alloc[OF spawn_inG])
  by (auto simp: valid_def upd_lock_def prod_n_valid_def \<epsilon>_n_valid valid_raw_ex_def)
  
lemma spawn_spec: "
{{{ WP (Val f$#[()]) {{ \<Psi> }} }}} 
  spawn $ Val f 
{{{ \<lambda>lv. \<exists>\<^sub>u l. (\<upharpoonleft>(lv = LitV (LitLoc l))) \<^emph> join_handle l \<Psi> }}}"
  apply iIntros subgoal for \<Phi>
  unfolding spawn_def
  apply brute_force_solver
  apply iwp_bind
  apply (iwp_pure rule: pure_exec_injl)
  apply iwp_val
  apply iwp_bind
  apply (iwp rule: wp_alloc')
  apply iwp_val
  apply iwp_beta
  apply iwp_seq
  apply (iApply rule: spawn_token_alloc)
  apply brute_force_solver
  apply fupd_elimL
  subgoal for l \<gamma>
  apply (iApply_step "?l\<mapsto>\<^sub>u?x" rule: inv_alloc[OF inv_inG, where ?P="spawn_inv \<gamma> l \<Psi>" and ?N=spawn_name])
  apply (entails_substR rule: upred_laterI) unfolding spawn_inv_def apply (iExistsR NoneV)
  apply fupd_elimL
  apply (iwp rule: wp_fork)
  apply last_resort
  apply (rule split_frame)
  apply (rule can_be_split_mono)
  prefer 2 apply (rule persistent_dupl') apply pers_solver apply (rule inv_inG)
  apply (rule can_be_split_sepR) apply (rule can_be_split_sepR) apply (rule can_be_split_baseL)
  apply (rule can_be_split_refl)
  subgoal 
    apply (iwp rule: wp_bind'[where ?C="\<lambda>x. Val (LitV (LitLoc l)) \<leftarrow> x"])
    apply (iwp rule: wp_bind'[where ?C="\<lambda>x. SomeE x"])
    apply (iwp rule: wp_wand)
    apply (iFrame2 "WP ?e {{ ?q}}")
    apply iIntros
    apply (check_moveL "inv ?n ?p")
    apply (iwp_pure rule: pure_exec_injr)
    apply iwp_val
    apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp])
    apply atomic_solver
    unfolding upred_later_exists
    apply iIntros subgoal for v x
    apply (split_move "l\<mapsto>\<^sub>u?x")
    apply (iwp rule: wp_store_texan)
    apply (check_moveR "\<triangleright>(l\<mapsto>\<^sub>u?x)")
    apply iFrame_single
    apply (rule upred_later_mono_extR)
    apply iIntros
    apply (entails_substR rule: fupd_intro[OF inv_inG])
    apply (iExistsR "SomeV v")
    apply (entails_substR rule: upred_laterI)
    apply (iFrame2 "l\<mapsto>\<^sub>u?x")
    apply (rule upred_disjIL) by iFrame_single
    done
  apply iris_simp
  apply (entails_substR rule: fupd_intro[OF inv_inG])+
  apply iwp_beta
  apply iwp_val
  apply (iApply rule: upred_universal_wand[where ?'b=val])
  unfolding join_handle_def spawn_inv_def
  by (iExistsR \<gamma>) done done 
  
lemma join_spec: "
{{{ join_handle l \<Psi> }}}
  join $ #[l]
{{{ \<Psi> }}}"
  unfolding join_handle_def
  apply iIntros subgoal for \<Phi> \<gamma>
  apply (check_moveL "\<triangleright>?p") apply (rule upred_wandE)
  apply (check_moveL "own put_spawn ?g ?e") apply (rule upred_wandE)
  apply (rule persistent_loebI) apply pers_solver apply (rule inv_inG)
  apply iIntros
  apply (subst (2) join_def)
  apply (iApply rule: upred_entail_eqL[OF upred_persis_later]) apply (iDrop "\<box> ?P")+
  apply (entails_substR rule: wp_pure_step_later[OF wp_inG pure_exec_beta, simplified])
  apply brute_force_solver
  apply (iwp rule: wp_bind'[where ?C="\<lambda>x. Case x _ _"])
  apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp])
  apply atomic_solver
  apply (subst spawn_inv_def) unfolding upred_later_exists apply iIntros
  apply (split_move "l\<mapsto>\<^sub>u?x")
  apply (iwp rule: wp_load_texan)
  apply brute_force_solver
  apply (check_moveL "?p \<or>\<^sub>u ?q")
  apply (rule upred_disjE')
  subgoal apply iIntros
    apply (iSplit "l\<mapsto>\<^sub>u?n" "\<triangleright>?p")
    prefer 2 subgoal apply iNext unfolding spawn_inv_def apply (iExistsR "NoneV") by iFrame_single
    apply (iwp_pure rule: pure_exec_case_injl)
    apply (iApply rule: upred_persisE)
    apply iApply_wand+
    apply iwp_beta
    apply (subst (2) join_def) by iFrame_single
  apply iIntros
  apply (rule upred_disjE')
  subgoal for v w
    apply (iSplit "own put_spawn ?g ?e \<^emph> (l\<mapsto>\<^sub>u?n)" "\<triangleright>?p")
    prefer 2 subgoal apply iNext unfolding spawn_inv_def apply (iExistsR "SomeV w")
    apply (iFrame2 "l\<mapsto>\<^sub>u?x") apply (rule upred_disjIR) by iFrame_single
    apply (iwp_pure_later rule: pure_exec_case_injr)
    apply (check_moveL "\<triangleright>?p") apply (rule upred_later_mono_extR)
    apply iwp_beta
    apply iwp_val
    apply (iApply rule: upred_universal_wand) 
    by iFrame_single
  apply (iApply_step2 "\<upharpoonleft>False" "own put_spawn \<gamma> ex.Ex ()")
  apply (subst upred_sep_comm)  
  by (iDestruct rule: inG.own_valid2[OF spawn_inG])
done

lemma par_spec: "WP (Val f1) $ #[()] {{ \<Psi>1 }} -\<^emph> WP (Val f2) $ #[()] {{ \<Psi>2 }} -\<^emph> 
  (\<triangleright> (\<forall>\<^sub>u v1 v2. (\<Psi>1 v1 \<^emph> \<Psi>2 v2) -\<^emph> \<triangleright> \<Phi> (PairV v1 v2))) -\<^emph> WP par $ f1 $ f2 {{ \<Phi> }}"
  apply iIntros
  unfolding par_def
  apply (subst (1) lambda_to_ectxt)
  apply (entails_substR rule: wp_bind[OF wp_inG])
  apply iwp_beta
  apply (iwp_pure rule: pure_exec_rec)
  apply iwp_val
  apply (subst lang_ctxt.simps) unfolding fill_item.simps
  apply iwp_beta
  apply (iwp rule: wp_let_bind)
  apply (iwp rule: spawn_spec)
  apply (iFrame2 "WP (Val f1) $ UnitE {{ ?q }}")
  apply (rule upred_later_mono_extR) apply iIntros
  apply iwp_beta
  apply (iwp rule: wp_let_bind)
  apply (iwp rule: wp_wand)
  apply (iFrame2 "WP (Val f2) $ UnitE {{ ?q }}")
  apply iIntros
  apply iwp_beta
  apply iwp_bind
  apply (iwp rule: join_spec)
  apply (iFrame2 "join_handle ?l ?p")
  apply iNext
  apply iIntros
  apply iwp_beta
  apply (iwp_pure_later rule: pure_exec_pair)
  subgoal for vl l v2 v1
  apply (iForallL v1, iForallL v2) apply (iApply_wand_as_rule "\<Psi>1 v1 \<^emph> \<Psi>2 v2" "\<Psi>1 v1 \<^emph> \<Psi>2 v2")
  apply iFrame_single
  apply (rule upred_later_mono)
  by (iwp rule: wp_value) done

lemma par_wp: "WP e1 {{ \<Psi>1 }} -\<^emph> WP e2 {{ \<Psi>2 }} -\<^emph> 
  (\<triangleright> (\<forall>\<^sub>u v1 v2. (\<Psi>1 v1 \<^emph> \<Psi>2 v2) -\<^emph> \<triangleright> \<Phi> (PairV v1 v2))) -\<^emph> WP (e1 ||| e2) {{ \<Phi> }}"
  apply iIntros
  \<comment> \<open>Make the expressions \<^term>\<open>E\<lambda> None: e1\<close> into \<^term>\<open>V\<lambda> None: e1\<close>\<close>
  apply (subst (2) lambda_to_ectxt_arg)
  apply iwp_bind
  apply (iwp_pure rule: pure_exec_rec) apply iwp_val
  apply iwp_bind
  apply (iwp_pure rule: pure_exec_rec) apply iwp_val
  \<comment> \<open>Apply @{thm par_spec}\<close>
  apply (entails_substR rule: par_spec) apply iFrame_single
  by (rule upred_sep_mono; iwp_beta)
end
end