theory RWSpinLockClient
imports RWSpinLock "./HeapLang/ParSpec" "./IrisCore/FracAuth"
begin

section \<open>Simple client of the RWSpinLock\<close>

\<comment> \<open>Reset resets the data counters and sets the mode according to the even flag.\<close>
definition reset :: val where "reset \<equiv>
  \<comment> \<open>Globals as explicit params\<close>
  V\<lambda> Some ''rwl'':
  E\<lambda> Some ''mode'':
  E\<lambda> Some ''data0'':
  E\<lambda> Some ''data1'':
  \<comment> \<open>Actual function\<close>
  E\<lambda> Some ''even'' :
    (acquire_excl $ (V ''rwl'');;
    if: (V ''even'') 
      then ((V ''mode'') \<leftarrow> #[2::int];;
            (V ''data0'') \<leftarrow> #[0::int];;
            (V ''data1'') \<leftarrow> #[0::int])
      else ((V ''mode'') \<leftarrow> #[1::int];;
            (V ''data0'') \<leftarrow> #[0::int];;
            (V ''data1'') \<leftarrow> #[0::int])
    endif;;
    release_excl $ (V ''rwl''))"

\<comment> \<open>Increment reads the mode and increases the data counters accordingly.\<close>
definition increment :: val where "increment \<equiv>
  \<comment> \<open>Globals as explicit params\<close>
  V\<lambda> Some ''rwl'':
  E\<lambda> Some ''mode'':
  E\<lambda> Some ''data0'':
  E\<lambda> Some ''data1'':
  \<comment> \<open>Actual function\<close>
    (acquire_shared $ (V ''rwl'');;
    (let: (Some ''incr'') := ! (V ''mode'') in
    FAA (V ''data0'') (V ''incr'');;
    FAA (V ''data1'') (V ''incr'');;
    release_shared $ (V ''rwl'')
    endlet))"

\<comment> \<open>An exemplary client with allocation of the heap cells and lock as well as some parallel 
  execution of the reset and increment functions.\<close>
definition client where "client \<equiv>
  let: Some ''data0'' := Ref #[0::int] in
  let: Some ''data1'' := Ref #[0::int] in
  let: Some ''mode'' := Ref #[1::int] in
  let: Some ''rwl'' := RWSpinLock.newlock $ #[()] in

  (((reset $ (V ''rwl'') $ (V ''mode'') $ (V ''data0'') $ (V ''data1'') $ #[True]);;
  (increment $ (V ''rwl'') $ (V ''mode'') $ (V ''data0'') $ (V ''data1'')))
|||
  ((increment $ (V ''rwl'') $ (V ''mode'') $ (V ''data0'') $ (V ''data1''));;
  (increment $ (V ''rwl'') $ (V ''mode'') $ (V ''data0'') $ (V ''data1''));;
  (reset $ (V ''rwl'') $ (V ''mode'') $ (V ''data0'') $ (V ''data1'') $ #[False])))

  endlet endlet endlet endlet"
    
context  
fixes get_heap :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> heap_lang_heap option"
  and put_heap
  and get_inv :: "gname \<Rightarrow> 'res \<Rightarrow> inv option"
  and put_inv
  and get_proph :: "gname \<Rightarrow> 'res \<Rightarrow> (proph_id, val\<times>val) proph_mapGS option"
  and put_proph
  and get_rwlock :: "gname \<Rightarrow> 'res \<Rightarrow> rwlockG option"
  and put_rwlock
  and get_frac_auth :: "gname \<Rightarrow> 'res \<Rightarrow> int frac_auth option"
  and put_frac_auth
  and get_spawn :: "gname \<Rightarrow> 'res \<Rightarrow> spawn_token option"
  and put_spawn
assumes heap_inG[heap_inG_axiom]: "inG get_heap put_heap"
  and inv_inG[inv_inG_axiom]: "inG get_inv put_inv"
  and prophm_inG[proph_inG_axiom]: "inG get_proph put_proph"
  and rwlock_inG[log_prog_rule]: "inG get_rwlock put_rwlock"
  and frac_auth_inG[log_prog_rule]: "inG get_frac_auth put_frac_auth"
  and spawn_inG[log_prog_rule]: "inG get_spawn put_spawn"
begin
  
text \<open>Boilerplate setup\<close>
lemmas wp_inG[inG_axioms] = inv_inG heap_inG prophm_inG
abbreviation fancy_upd' ("\<Turnstile>{_,_}=>_") where "fancy_upd' \<equiv> ViewShift.fancy_upd put_inv"
abbreviation wand_fupd' ("_={_,_}=\<^emph>_") where "wand_fupd' \<equiv> ViewShift.wand_fupd put_inv"
abbreviation points_to_own' ("_\<mapsto>{#_}_" 60) where "points_to_own' \<equiv> AuthHeap.points_to_own put_heap"
abbreviation points_to_full' (infix "\<mapsto>\<^sub>u" 60) where "points_to_full' \<equiv> AuthHeap.points_to_full put_heap"
abbreviation atomic_hoare' ("\<langle>_\<rangle>/ _ @ _/ \<langle> _,RET _ \<rangle>") where "atomic_hoare' \<equiv> WeakestPrecondition.atomic_hoare put_inv put_heap put_proph"
abbreviation WP' ("WP _ {{ _ }}") where "WP e {{ Q }} \<equiv> WeakestPrecondition.WP put_inv put_heap put_proph e Q"
abbreviation wand_linear_fupd' ("_={_}=\<^emph>_") where "wand_linear_fupd' \<equiv> ViewShift.wand_linear_fupd put_inv"
abbreviation linear_fupd' ("\<Turnstile>{_}=>_") where "linear_fupd' \<equiv> ViewShift.linear_fupd put_inv"
abbreviation texan' ("{{{ _ }}} _ {{{ _ }}}") where "texan' \<equiv> WeakestPrecondition.texan put_inv put_heap put_proph"
abbreviation inv' where "inv' \<equiv> Invariant.inv put_inv"
abbreviation is_rw_lock' where "is_rw_lock' \<equiv> RWSpinLock.is_rw_lock put_rwlock put_heap put_inv"
abbreviation fa_own where "fa_own \<equiv> inG.own put_frac_auth"

definition modeN :: namespace where "modeN = add_name rwlock_name (string_to_name ''mode'')"
definition data0N :: namespace where "data0N = add_name rwlock_name (string_to_name ''data0'')"
definition data1N :: namespace where "data1N = add_name rwlock_name (string_to_name ''data1'')"

definition data0_name :: gname where "data0_name = 45"
definition data1_name :: gname where "data1_name = 46"

\<comment> \<open>Only the exclusive lock gives access to change the mode. Moreover, shared access grants access 
  to the data counters, but only through invariants to achieve truly shared access.
  The program invariants uphold by the example are:
  - if the lock is not shared, then the data counters have the same values
  - if the lock is not exclusively owned, the data counters are always multiples of the mode
  These invariants are enforced through fractional authoritative tokens.\<close>
definition lock_res :: "loc \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> frac \<Rightarrow> 'res upred_f" where
  "lock_res mode_l data0_l data1_l q \<equiv>
    \<exists>\<^sub>u (mode_v::int) incr. 
      (\<upharpoonleft>(incr \<ge> 0 \<and> (mode_v = 1 \<or> mode_v = 2) \<and> (incr mod mode_v = 0)))
      \<^emph> (\<upharpoonleft>(q\<le>1))
      \<^emph> (mode_l \<mapsto>{# q} #[mode_v])
      \<^emph> inv' data0N (\<exists>\<^sub>udata0_v. (data0_l \<mapsto>\<^sub>u #[data0_v]) \<^emph> fa_own data0_name (\<Zspot>F data0_v) \<^emph> (\<upharpoonleft>(data0_v\<ge>0)))
      \<^emph> inv' data1N (\<exists>\<^sub>udata1_v. (data1_l \<mapsto>\<^sub>u #[data1_v]) \<^emph> fa_own data1_name (\<Zspot>F data1_v) \<^emph> (\<upharpoonleft>(data1_v\<ge>0)))
      \<^emph> fa_own data0_name (\<circle>F{q} incr) \<^emph> fa_own data1_name (\<circle>F{q} incr)"

lemma lock_res_fractional: "fractional (lock_res mode_l data0_l data1_l)"
apply (auto simp: fractional_def lock_res_def upred_entail_eq_def; iIntros)
subgoal for p q mode_v incr_token
  apply (iExistsR mode_v, iExistsR incr_token)
  apply (iExistsR mode_v, iExistsR 0)
  apply (rule upred_entails_trans[OF _ frameE[of _ _ "inv' data0N _ \<^emph> inv' data0N _"]], prefer_last)
  apply (rule frame_sepL, rule frame_sepL, rule frame_sepL, rule frame_sepR, rule frame_sepL,
    rule frame_sepL, rule frame_sepL, rule frame_sepL, rule frame_sepL, rule frame_refl, iris_simp)
  apply (entails_substR rule: persistent_goal_dupl, log_prog_solver)
  apply iFrame_single
  apply (rule upred_entails_trans[OF _ frameE[of _ _ "inv' data1N _ \<^emph> inv' data1N _"]], prefer_last)
  apply (rule frame_sepL, rule frame_sepL, rule frame_sepR, rule frame_sepL, rule frame_sepL, 
    rule frame_sepL, rule frame_sepL, rule frame_refl, iris_simp)
  apply (rule persistent_goal_dupl[where ?Q="inv' _ _"], log_prog_solver)
  apply iFrame_single
  apply (lift_frame "mode_l\<mapsto>{#p}?x",check_moveR "mode_l\<mapsto>{#q}?x")
  apply (entails_substR rule: points_to_split[OF heap_inG])
  apply (simp add: op_dfrac_def frac_op_plus)
  apply iFrame_single
  apply (check_moveR "fa_own data0_name \<circle>F{p} 0",check_moveR "fa_own data0_name \<circle>F{q} ?x")
  apply (entails_substR rule: upred_entail_eqL[OF inG.own_op[OF frac_auth_inG]])
  apply (check_moveR "fa_own data1_name \<circle>F{p} 0",check_moveR "fa_own data1_name \<circle>F{q} ?x")
  apply (entails_substR rule: upred_entail_eqL[OF inG.own_op[OF frac_auth_inG]])
  apply (simp add: frac_auth_frag_op int_op_plus)
  apply iFrame_single+
  apply (transfer, simp) apply iPureR by (transfer, simp)
subgoal for p q mode_v incr_token mode_v' incr_token'
  apply (iExistsR mode_v, iExistsR "incr_token'+incr_token")
  apply (split_move "inv' data1N ?p")
  apply (split_move "inv' data0N ?p") 
  apply (iDrop "inv' data0N ?p", iDrop "inv' data0N ?p") 
  apply (iDrop "inv' data1N ?p", iDrop "inv' data1N ?p")
  apply (check_moveR "inv' data1N ?p", check_moveR "inv' data0N ?p")
  apply iFrame_single apply iFrame_single
  apply (split_move "mode_l\<mapsto>{#p}?x",split_move "mode_l\<mapsto>{#q}?x")
  apply (entails_substL rule: points_to_combine[OF heap_inG], iPureL)
  apply (iDestruct rule: points_to_valid[OF heap_inG])
  apply (simp add: op_dfrac_def frac_op_plus)
  apply (iFrame "mode_l\<mapsto>{#p+q}?x")
  apply (iDrop "inv' data0N ?p", iDrop "inv' data1N ?p")
  apply (iDrop "inv' data0N ?p", iDrop "inv' data1N ?p")
  apply (split_move "fa_own data1_name \<circle>F{p} ?y",split_move "fa_own data1_name \<circle>F{q} ?x")
  apply (entails_substL rule: upred_entail_eqR[OF inG.own_op[OF frac_auth_inG]])
  apply (check_moveL "fa_own data0_name \<circle>F{p} ?y",check_moveL "fa_own data0_name \<circle>F{q} ?x")
  apply (entails_substL rule: upred_entail_eqR[OF inG.own_op[OF frac_auth_inG]])
  apply (simp add: frac_auth_frag_def op_view_def view_frag_def op_option_def op_prod_def frac_op_plus
      int_op_plus view_auth_def op_dfrac_def \<epsilon>_int_def ag_idem)
  apply iFrame_single apply iFrame_single 
  apply (cases "p+q=1")
  apply (frule frac_sum_one_le)
  prefer 2 apply (iAssert_pers "\<upharpoonleft>(p+q<1)") apply iPureR 
  apply (simp add: valid_def valid_raw_dfrac_def valid_raw_frac_def iris_simp)
  apply (metis less_eq_frac.rep_eq one_frac.rep_eq order_less_le)
  apply (rule upred_pure_impl_emp)
  apply auto by iPureR+
done
  
lemma reset_spec: "
{{{ is_rw_lock' \<gamma> #[rwl] (lock_res mode_l data0_l data1_l) }}}
  (reset $ #[rwl::loc] $ #[mode_l] $ #[data0_l] $ #[data1_l] $ #[e::bool])
{{{ \<lambda>_. is_rw_lock' \<gamma> #[rwl] (lock_res mode_l data0_l data1_l) }}}"
  apply iIntros subgoal for \<Phi>
  unfolding reset_def
  \<comment> \<open>Do beta contraction\<close>
  apply (iwp_bind, iwp_beta, iwp_pure rule: pure_exec_rec, iwp_val)+
  apply iwp_beta
  apply iwp_seq
  \<comment> \<open>Acquire the lock\<close>
  apply (iwp rule: acquire_excl_spec[OF rwlock_inG])
  apply (iFrame "is_rw_lock' ?g ?l ?p") apply iNext
  apply iIntros
  apply iwp_beta
  \<comment> \<open>Split cases of if-then-else\<close>
  apply (cases e;simp)
  subgoal
    apply (iwp_pure rule: pure_exec_if_true)
    apply iwp_seq
    apply (subst lock_res_def)
    apply iIntros
    \<comment> \<open>Store the new mode\<close>
    apply (iwp rule: wp_store_texan)
    apply (iFrame "mode_l\<mapsto>\<^sub>u?x", iDrop "inv' data0N ?p", iDrop "inv' data1N ?p", iDrop "is_rw_lock' ?g ?l ?p")
    apply iNext apply iIntros
    apply iwp_beta
    \<comment> \<open>Store data0\<close>
    apply (check_moveL "inv' data0N ?p")
    apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
      elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver, iDrop "inv' data0N ?p")
    apply iIntros
    apply (iwp rule: wp_store_texan)
    apply (iFrame2 "data0_l\<mapsto>\<^sub>u?x")
    apply (rule upred_later_mono_extR)
    apply iIntros
    \<comment> \<open>Update the corresponding ghost state\<close>
    apply (check_move_all True "fa_own data0_name \<Zspot>F ?g \<^emph> fa_own data0_name \<circle>F{1} ?x")
    apply (iDestruct rule: inG.own_valid2[OF frac_auth_inG])
    apply (iApply rule: upred_entail_eqR[OF inG.own_op[OF frac_auth_inG]])
    apply (iApply rule: inG.own_update[OF frac_auth_inG, where ?b="\<Zspot>F 0 \<cdot> \<circle>F{1} 0"])
    subgoal by (rule put_update[OF frac_auth_inG], rule int_fa_lup, drule valid_frac_auth_eq, simp)
    apply (rule bupd_elim(2)[OF inv_inG])
    apply fupd_elimL
    apply (iApply rule: upred_entail_eqL[OF inG.own_op[OF frac_auth_inG]])
    apply (entails_substR rule: fupd_intro[OF inv_inG])
    apply (iExistsR 0)
    apply (iSplitR "data0_l\<mapsto>\<^sub>u?x \<^emph> fa_own data0_name \<Zspot>F 0" "\<triangleright>?p") apply iNext apply iFrame_single+
    apply iwp_beta
    \<comment> \<open>Store data1\<close>
    apply (check_moveL "inv' data1N ?p")
    apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
      elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver, iDrop "inv' data1N ?p")
    apply iIntros
    apply (iwp rule: wp_store_texan)
    apply (iFrame2 "data1_l\<mapsto>\<^sub>u?x")
    apply (rule upred_later_mono_extR)
    apply iIntros
    \<comment> \<open>Update the corresponding ghost state\<close>
    apply (split_move "fa_own data1_name \<circle>F{1} ?x \<^emph> fa_own data1_name \<Zspot>F ?g")
    apply (check_moveL "fa_own data1_name \<circle>F{1} ?x")
    apply (iDestruct rule: inG.own_valid2[OF frac_auth_inG])
    apply (iApply rule: upred_entail_eqR[OF inG.own_op[OF frac_auth_inG]])
    apply (iApply rule: inG.own_update[OF frac_auth_inG, where ?b="\<Zspot>F 0 \<cdot> \<circle>F{1} 0"])
    subgoal by (rule put_update[OF frac_auth_inG], rule int_fa_lup, drule valid_frac_auth_eq, simp)
    apply (rule bupd_elim(2)[OF inv_inG])
    apply fupd_elimL
    apply (iApply rule: upred_entail_eqL[OF inG.own_op[OF frac_auth_inG]])
    apply (entails_substR rule: fupd_intro[OF inv_inG])
    apply (iExistsR 0)+
    apply (iSplitR "data1_l\<mapsto>\<^sub>u?x \<^emph> fa_own data1_name \<Zspot>F 0" "\<triangleright>?p", iNext,iFrame_single+)
    apply iwp_beta
    \<comment> \<open>Release the lock\<close>
    apply (iwp rule: release_excl_spec[OF rwlock_inG])
    apply (check_moveR "excl_locked ?p ?g") apply iFrame_single
    apply (split_move "is_rw_lock' ?g ?l ?p", check_moveR "is_rw_lock' ?g ?l ?p", iFrame_single)
    apply (subst lock_res_def)
    by brute_force_solver
  subgoal
    apply (iwp_pure rule: pure_exec_if_false)
    apply iwp_seq
    apply (subst lock_res_def)
    apply iIntros
    \<comment> \<open>Store the new mode\<close>
    apply (iwp rule: wp_store_texan)
    apply (iFrame "mode_l\<mapsto>\<^sub>u?x", iDrop "inv' data0N ?p", iDrop "inv' data1N ?p", iDrop "is_rw_lock' ?g ?l ?p")
    apply iNext apply iIntros
    apply iwp_beta
    apply (check_moveL "inv' data0N ?p")
    apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
      elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver, iDrop "inv' data0N ?p")
    apply iIntros
    \<comment> \<open>Store data0\<close>
    apply (iwp rule: wp_store_texan)
    apply (iFrame2 "data0_l\<mapsto>\<^sub>u?x")
    apply (rule upred_later_mono_extR)
    apply iIntros
    \<comment> \<open>Update the corresponding ghost state\<close>
    apply (check_move_all True "fa_own data0_name \<Zspot>F ?g \<^emph> fa_own data0_name \<circle>F{1} ?x")
    apply (iDestruct rule: inG.own_valid2[OF frac_auth_inG])
    apply (iApply rule: upred_entail_eqR[OF inG.own_op[OF frac_auth_inG]])
    apply (iApply rule: inG.own_update[OF frac_auth_inG, where ?b="\<Zspot>F 0 \<cdot> \<circle>F{1} 0"])
    subgoal by (rule put_update[OF frac_auth_inG], rule int_fa_lup, drule valid_frac_auth_eq, simp)
    apply (rule bupd_elim(2)[OF inv_inG])
    apply fupd_elimL
    apply (iApply rule: upred_entail_eqL[OF inG.own_op[OF frac_auth_inG]])
    apply (entails_substR rule: fupd_intro[OF inv_inG])
    apply (iExistsR 0)
    apply (iSplitR "data0_l\<mapsto>\<^sub>u?x \<^emph> fa_own data0_name \<Zspot>F 0" "\<triangleright>?p", iNext,iFrame_single+)
    apply iwp_beta
    \<comment> \<open>Store data1\<close>
    apply (check_moveL "inv' data1N ?p")
    apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
      elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver, iDrop "inv' data1N ?p")
    apply iIntros
    apply (iwp rule: wp_store_texan)
    apply (iFrame2 "data1_l\<mapsto>\<^sub>u?x")
    apply (rule upred_later_mono_extR)
    apply iIntros
    \<comment> \<open>Update the corresponding ghost state\<close>
    apply (split_move "fa_own data1_name \<Zspot>F ?g \<^emph> fa_own data1_name \<circle>F{1} ?x")
    apply (check_moveL "fa_own data1_name \<circle>F{1} ?x")
    apply (iDestruct rule: inG.own_valid2[OF frac_auth_inG])
    apply (iApply rule: upred_entail_eqR[OF inG.own_op[OF frac_auth_inG]])
    apply (iApply rule: inG.own_update[OF frac_auth_inG, where ?b="\<Zspot>F 0 \<cdot> \<circle>F{1} 0"])
    subgoal by (rule put_update[OF frac_auth_inG], rule int_fa_lup, drule valid_frac_auth_eq, simp)
    apply (rule bupd_elim(2)[OF inv_inG])
    apply fupd_elimL
    apply (iApply rule: upred_entail_eqL[OF inG.own_op[OF frac_auth_inG]])
    apply (entails_substR rule: fupd_intro[OF inv_inG])
    apply (iExistsR 0)+
    apply (iSplitR "data1_l\<mapsto>\<^sub>u?x \<^emph> fa_own data1_name \<Zspot>F 0" "\<triangleright>?p", iNext,iFrame_single+)
    apply iwp_beta
    \<comment> \<open>Release the lock\<close>
    apply (iwp rule: release_excl_spec[OF rwlock_inG])
    apply (check_moveR "excl_locked ?p ?g", iFrame_single)
    apply (split_move "is_rw_lock' ?g ?l ?p", check_moveR "is_rw_lock' ?g ?l ?p", iFrame_single)
    apply (subst lock_res_def)
    by brute_force_solver
  done
done  

lemma increment_spec: "
  {{{ is_rw_lock' \<gamma> #[rwl] (lock_res mode_l data0_l data1_l) }}}
    (increment $ #[rwl::loc] $ #[mode_l] $ #[data0_l] $ #[data1_l])
  {{{ \<lambda>_. is_rw_lock' \<gamma> #[rwl] (lock_res mode_l data0_l data1_l) }}}"
  apply iIntros subgoal for \<Phi>
  unfolding increment_def
  \<comment> \<open>Do beta contraction\<close>
  apply (iwp_bind, iwp_beta, iwp_pure rule: pure_exec_rec, iwp_val)+
  apply iwp_beta
  apply iwp_seq
  \<comment> \<open>Acquire the lock\<close>
  apply (iwp rule: acquire_shared_spec[OF rwlock_inG])
  apply (iFrame "is_rw_lock' ?g ?l ?p")
  apply iNext
  apply (subst lock_res_def)
  apply iIntros
  apply iwp_beta
  apply iwp_bind
  \<comment> \<open>Load the mode\<close>
  apply (iwp rule: wp_load_texan)
  apply (iFrame2 "mode_l\<mapsto>{#?d}?x")
  apply iNext
  apply iIntros
  apply iwp_beta
  \<comment> \<open>FAA data0\<close>
  subgoal for q mode_i incr_token mode_v
  apply iwp_seq
  apply (check_moveL "inv' data0N ?p")
  apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
    elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver, iDrop "inv' data0N ?p")
  apply iIntros subgoal for data0_v
  apply (iwp rule: wp_faa) prefer 2 using valid_dfrac_own apply blast
  apply (split_move "data0_l\<mapsto>\<^sub>u?x", lift_frame "\<triangleright>data0_l\<mapsto>\<^sub>u?x") apply iFrame_single
  apply (rule upred_later_mono_extR)
  apply iIntros
  \<comment> \<open>Update the corresponding ghost state\<close>
  apply (check_move_all True "fa_own data0_name \<Zspot>F data0_v \<^emph> fa_own data0_name \<circle>F{q} incr_token")
  apply (iDestruct rule: inG.own_valid2[OF frac_auth_inG])
  apply (iApply rule: upred_entail_eqR[OF inG.own_op[OF frac_auth_inG]])
  apply (iApply rule: inG.own_update[OF frac_auth_inG put_update[OF frac_auth_inG, where 
    ?b="\<Zspot>F (data0_v+mode_i) \<cdot> \<circle>F{q} (incr_token+mode_i)"]])
  apply (rule int_fa_lup, simp)
  apply (rule bupd_elim(2), log_prog_solver, fupd_elimL)
  apply (iApply rule: upred_entail_eqL[OF inG.own_op[OF frac_auth_inG]])
  apply (entails_substR rule: fupd_intro[OF inv_inG])
  apply (iExistsR "data0_v+mode_i")+
  apply (iSplit "data0_l\<mapsto>\<^sub>u?x \<^emph> fa_own data0_name \<Zspot>F ?y" "\<triangleright>?p")
  prefer 2 apply iNext apply iPureR apply linarith apply (split_move "data0_l\<mapsto>\<^sub>u?x") 
  apply (rule framing) apply frame_solver
  apply iFrame_single+
  apply iwp_beta
  \<comment> \<open>FAA data1\<close>
  apply (check_moveL "inv' data1N ?p")
  apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
    elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver, iDrop "inv' data1N ?p")
  apply iIntros subgoal for _ data1_v
  apply (iwp rule: wp_faa) prefer 2 using valid_dfrac_own apply blast
  apply (iFrame2 "data1_l\<mapsto>\<^sub>u?x")
  apply (rule upred_later_mono_extR)
  apply iIntros
  \<comment> \<open>Update the corresponding ghost state\<close>
  apply (check_move_all True "fa_own data1_name \<Zspot>F data1_v \<^emph> fa_own data1_name \<circle>F{q} incr_token")
  apply (iDestruct rule: inG.own_valid2[OF frac_auth_inG])
  apply (iApply rule: upred_entail_eqR[OF inG.own_op[OF frac_auth_inG]])
  apply (iApply rule: inG.own_update[OF frac_auth_inG put_update[OF frac_auth_inG, where 
    ?b="\<Zspot>F (data1_v+mode_i) \<cdot> \<circle>F{q} (incr_token+mode_i)"]])
  apply (rule int_fa_lup, simp)
  apply (rule bupd_elim(2), log_prog_solver, fupd_elimL)
  apply (iApply rule: upred_entail_eqL[OF inG.own_op[OF frac_auth_inG]])
  apply (entails_substR rule: fupd_intro[OF inv_inG])
  apply (iExistsR "data1_v+mode_i")+
  apply (iSplit "data1_l\<mapsto>\<^sub>u?x \<^emph> fa_own data1_name \<Zspot>F ?y" "\<triangleright>?p")
  prefer 2 apply iNext apply iPureR apply linarith apply (split_move "data1_l\<mapsto>\<^sub>u?x") 
  apply (rule framing) apply frame_solver
  apply iFrame_single+
  apply iwp_beta
  \<comment> \<open>Release the lock\<close>
  apply (iwp rule: release_shared_spec[OF rwlock_inG])
  apply (check_moveR "shared_locked ?p ?f ?g") apply iFrame_single
  apply (check_moveR "is_rw_lock' ?g ?l ?p") apply iFrame_single
  apply (subst lock_res_def)
  by brute_force_solver  
done done done done

\<comment> \<open>Just show that the client can be executed based on the above specifications using \<^term>\<open>lock_res\<close>.\<close>
lemma client_spec: "{{{ emp }}} client {{{ \<lambda>_. emp }}}"
  unfolding client_def
  apply iIntros
  \<comment> \<open>Allocate the global variables\<close>
  apply (iwp_bind, iwp rule: wp_alloc', iwp_val, iwp_beta)
  apply (iwp_bind, iwp rule: wp_alloc', iwp_val, iwp_beta)
  apply (iwp_bind)
  \<comment> \<open>Construct the ghost state and invariants\<close>
  apply (entails_substL rule: add_holds[OF inG.own_alloc[OF frac_auth_inG frac_auth_zero_valid, of data0_name]])
  apply (rule bupd_elim(2), log_prog_solver, fupd_elimL)
  apply (entails_substL rule: add_holds[OF inG.own_alloc[OF frac_auth_inG frac_frag_zero_valid, of data0_name]])
  apply (rule bupd_elim(2), log_prog_solver, fupd_elimL)
  apply (entails_substL rule: add_holds[OF inG.own_alloc[OF frac_auth_inG frac_auth_zero_valid, of data1_name]])
  apply (rule bupd_elim(2), log_prog_solver, fupd_elimL)
  apply (entails_substL rule: add_holds[OF inG.own_alloc[OF frac_auth_inG frac_frag_zero_valid, of data1_name]])
  apply (rule bupd_elim(2), log_prog_solver, fupd_elimL)
  subgoal for \<phi> data0_l data1_l
  apply (iMod rule: inv_alloc[OF inv_inG, where ?N=data0N and ?P="(\<exists>\<^sub>udata0. (data0_l\<mapsto>\<^sub>u#[data0])
    \<^emph> fa_own data0_name (\<Zspot>F data0) \<^emph> (\<upharpoonleft>(data0\<ge>0)))"])
  apply (iApply_wand_as_rule "?x" "data0_l\<mapsto>\<^sub>u?y\<^emph> fa_own data0_name \<Zspot>F 0")
  apply (iExistsR 0)+ apply iNext apply fupd_elimL
  apply (iMod rule: inv_alloc[OF inv_inG, where ?N=data1N and ?P="(\<exists>\<^sub>udata1. (data1_l\<mapsto>\<^sub>u#[data1])
    \<^emph> fa_own data1_name (\<Zspot>F data1) \<^emph> (\<upharpoonleft>(data1\<ge>0)))"])
  apply (iApply_wand_as_rule "?x" "data1_l\<mapsto>\<^sub>u?y\<^emph> fa_own data1_name \<Zspot>F 0")
  apply (iExistsR 0)+ apply iNext apply iFrame_single+ apply fupd_elimL
  apply (iwp rule: wp_alloc') subgoal for mode_l
  apply iwp_val
  apply (entails_substR rule: fupd_intro[OF inv_inG])+
  apply iwp_beta
  apply iwp_bind
  \<comment> \<open>Put the resources into the lock\<close>
  apply (iwp rule: RWSpinLock.newlock_spec'[OF rwlock_inG, where ?Q="lock_res mode_l data0_l data1_l"])
  apply iwp_beta
  apply (iForallL "lock_res mode_l data0_l data1_l 1")
  apply (iApply_wand_as_rule "?p" "fa_own data0_name \<circle>F{1} 0 \<^emph> fa_own data1_name \<circle>F{1} 0 
    \<^emph> (mode_l\<mapsto>{#1}LitV (LitInt 1))")
  subgoal
    apply (iPureR, rule as_fractional_refl[OF lock_res_fractional])
    apply (subst lock_res_def) by brute_force_solver
  apply (entails_substR rule: fupd_wp[OF wp_inG], fupd_elimL, entails_substR rule: fupd_intro[OF inv_inG])
  apply (iDrop "inv' ?N ?p")+
  apply iExistsL
  apply (iwp rule: par_wp[OF spawn_inG, where ?\<Psi>1.0="\<lambda>_. emp" and ?\<Psi>2.0="\<lambda>_. emp"])
  apply (iSplit "is_rw_lock' ?g ?l ?p" "WP' ?e ?q")
  subgoal by (check_moveL "\<triangleright>?p", rule upred_later_mono_extR, iIntros, iNext, 
    rule upred_universal_wand, simp)
  apply (iSplit "?x" "WP (reset $ ?rw $ ?m $ ?d0 $ ?d1 $ ?b ;; ?e) {{ ?q }}")
  \<comment> \<open>Prove both threads\<close>
  subgoal
    apply iwp_seq
    apply (iwp rule: increment_spec)
    apply (iFrame "is_rw_lock' ?g ?l ?p")
    apply iNext apply iIntros
    apply iwp_beta
    apply (iwp rule: increment_spec)
    apply (iFrame "is_rw_lock' ?g ?l ?p")
    apply iNext apply iIntros
    apply iwp_beta
    apply (iwp rule: reset_spec)
    by brute_force_solver
  subgoal
    apply iwp_seq  
    apply (iwp rule: reset_spec)
    apply (iFrame "is_rw_lock' ?g ?l ?p")
    apply iNext apply iIntros
    apply iwp_beta
    apply (iwp rule: increment_spec)
    by brute_force_solver
done done done
end
end