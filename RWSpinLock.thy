theory RWSpinLock
imports "./SpinLock/Demo"
begin

\<comment> \<open>Based on \<^url>\<open>https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lib/rw_spin_lock.v\<close>\<close>

definition newlock :: val where "newlock \<equiv> V\<lambda> None: Ref #[0::int]"

definition try_acquire_shared :: val where "try_acquire_shared \<equiv>
  V\<lambda> Some ''l'':
    let: Some ''n'' := !(V ''l'') in
    if: BinOp LeOp #[0::int] (V ''n'')
      then CAS (V ''l'') (V ''n'') (BinOp PlusOp (V ''n'') #[1::int])
      else FalseE 
    endif endlet"

definition acquire_shared :: val where "acquire_shared \<equiv>
  rec: (Some ''acquire'') (Some ''l'') :=
    if: try_acquire_shared $ (V ''l'')
      then UnitE
      else (V ''acquire'') $ (V ''l'')
    endif"

definition release_shared :: val where "release_shared \<equiv>
  V\<lambda> Some ''l'': (FAA (V ''l'') #[-1::int] ;; UnitE)"

definition try_acquire_excl :: val where "try_acquire_excl \<equiv>
  V\<lambda> Some ''l'': CAS (V ''l'') #[0::int] #[-1::int]"

definition acquire_excl :: val where "acquire_excl \<equiv>
  rec: (Some ''acquire'') (Some ''l'') :=
    if: try_acquire_excl $ (V ''l'')
      then UnitE
      else (V ''acquire'') $ (V ''l'')
    endif"

definition release_excl :: val where "release_excl \<equiv>
  V\<lambda> Some ''l'': (V ''l'' \<leftarrow> #[0::int])"

type_synonym rwlockG = "frac multiset view"

definition fractional :: "(frac \<Rightarrow> 'res::ucamera upred_f) \<Rightarrow> bool" where 
  "fractional \<Phi> \<equiv> \<forall>p q. (\<Phi> (p + q) \<stileturn>\<turnstile> (\<Phi> p \<^emph> \<Phi> q))"

definition as_fractional :: "'res upred_f \<Rightarrow> (frac \<Rightarrow> 'res::ucamera upred_f) \<Rightarrow> frac \<Rightarrow> bool" where
  "as_fractional P \<Phi> q \<equiv> P \<stileturn>\<turnstile> \<Phi> q \<and> fractional \<Phi>"

lemma as_fractional_refl: "fractional Q \<Longrightarrow> as_fractional (Q p) Q p"
  by (simp add: as_fractional_def)

lemma apply_as_fractional: "as_fractional P \<Phi> q \<Longrightarrow> P \<turnstile> \<Phi> q"
  by (simp add: as_fractional_def upred_entail_eq_def)

definition internal_fractional :: "(frac \<Rightarrow> 'res::ucamera upred_f) \<Rightarrow> 'res upred_f" where 
  "internal_fractional \<Phi> = \<box> (\<forall>\<^sub>u p q. (\<Phi> (p + q) -\<^emph> (\<Phi> p \<^emph> \<Phi> q)) \<and>\<^sub>u ((\<Phi> p \<^emph> \<Phi> q) -\<^emph> \<Phi> (p + q)))"
lemma [pers_rule,log_prog_rule]: "persistent (internal_fractional \<Phi>)"
  unfolding internal_fractional_def by pers_solver

lemma internal_fractional_iff: "\<box> (\<forall>\<^sub>u q. (\<Phi> q \<longrightarrow>\<^sub>u \<Psi> q) \<and>\<^sub>u (\<Psi> q \<longrightarrow>\<^sub>u \<Phi> q)) \<turnstile> (internal_fractional \<Phi> -\<^emph>
  internal_fractional \<Psi>)"
  unfolding internal_fractional_def
  apply iIntros
  apply (rule upred_entails_conjI)
  subgoal for p q
    apply iIntro
    apply (check_moveL "\<box>\<forall>\<^sub>uq. ((\<Phi> q \<longrightarrow>\<^sub>u \<Psi> q) \<and>\<^sub>u (\<Psi> q \<longrightarrow>\<^sub>u \<Phi> q))")
    apply (iApply rule: upred_persisE)
    apply (iForallL "p+q")
    apply (iApply rule: upred_weakeningR')
    apply (check_moveL "\<Psi> (p + q)")
    apply (iApply rule: upred_impl_apply')
    apply (check_moveL "\<box>(\<forall>\<^sub>uq p. (?p::frac \<Rightarrow> frac \<Rightarrow> _) q p)")
    apply (iApply rule: upred_persisE)
    apply (iForallL p, iForallL q)
    apply (iApply rule: upred_weakeningL')
    apply iApply_wand
    apply (check_moveL "\<box>\<forall>\<^sub>uq. ((\<Phi> q \<longrightarrow>\<^sub>u \<Psi> q) \<and>\<^sub>u (\<Psi> q \<longrightarrow>\<^sub>u \<Phi> q))")
    apply (iApply rule: upred_persisE)
    apply (iForallL p)
    apply (iApply rule: upred_weakeningL')
    apply (check_moveL "\<Phi> p")
    apply (iApply rule: upred_impl_apply')
    apply (iFrame2 "\<Psi> p")
    apply (iApply rule: upred_persisE)
    apply (iForallL q)
    apply (iApply rule: upred_weakeningL')
    apply (check_moveL "\<Phi> q")
    apply (iApply rule: upred_impl_apply')
    by (iFrame2 "\<Psi> q")
  subgoal for p q 
  apply iIntro
  apply (check_moveL "\<box>\<forall>\<^sub>uq. ((\<Phi> q \<longrightarrow>\<^sub>u \<Psi> q) \<and>\<^sub>u (\<Psi> q \<longrightarrow>\<^sub>u \<Phi> q))")
  apply (iApply rule: upred_persisE)
  apply (iForallL "p")
  apply (iApply rule: upred_weakeningR')
  apply (check_moveL "\<Psi> p")
  apply (iApply rule: upred_impl_apply')
  apply (check_moveL "\<box>\<forall>\<^sub>uq. ((\<Phi> q \<longrightarrow>\<^sub>u \<Psi> q) \<and>\<^sub>u (\<Psi> q \<longrightarrow>\<^sub>u \<Phi> q))")
  apply (iApply rule: upred_persisE)
  apply (iForallL "q")
  apply (iApply rule: upred_weakeningR')
  apply (check_moveL "\<Psi> q")
  apply (iApply rule: upred_impl_apply')
  apply (check_moveL "\<box>(\<forall>\<^sub>uq p. (?p::frac \<Rightarrow> frac \<Rightarrow> _) q p)")
  apply (iApply rule: upred_persisE)
  apply (iForallL p, iForallL q)
  apply (iApply rule: upred_weakeningR')
  apply (split_move_allO "(\<Phi> p \<^emph> \<Phi> q) \<^emph> (\<Phi> p \<^emph> \<Phi> q -\<^emph> \<Phi> (p + q))")
  apply (subst (2) upred_sep_assoc_eq[symmetric])
  apply (subst (2) upred_sep_assoc_eq[symmetric])
  apply (rule upred_entails_substE[OF upred_wand_apply])
  apply (check_moveL "\<box>\<forall>\<^sub>uq. ((\<Phi> q \<longrightarrow>\<^sub>u \<Psi> q) \<and>\<^sub>u (\<Psi> q \<longrightarrow>\<^sub>u \<Phi> q))")
  apply (iApply rule: upred_persisE)
  apply (iForallL "p + q")
  apply (iApply rule: upred_weakeningL')
  apply (check_moveL "\<Phi> (p + q)")
  apply (iApply rule: upred_impl_apply')
  by iFrame_single
done

lemma fractional_internal_fractional: "fractional Q \<Longrightarrow> upred_holds (internal_fractional Q)"
  unfolding fractional_def internal_fractional_def upred_entail_eq_def
  apply iIntros
  apply (rule upred_entails_conjI)
  by iIntros

lemma frac_add_comp_fun_commute: "comp_fun_commute ((+)::frac\<Rightarrow>frac\<Rightarrow>frac)"
  by (auto simp: comp_fun_commute_def comp_def add_ac)

context 
fixes get_rwlock :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> rwlockG option"
  and put_rwlock
  and get_heap :: "gname \<Rightarrow> 'res \<Rightarrow> heap_lang_heap option"
  and put_heap
  and get_inv :: "gname \<Rightarrow> 'res \<Rightarrow> inv option"
  and put_inv
  and get_proph :: "gname \<Rightarrow> 'res \<Rightarrow> (proph_id, val\<times>val) proph_mapGS option"
  and put_proph
assumes rwlock_inG: "inG get_rwlock put_rwlock"
  and inv_inG[inv_inG_axiom]: "inG get_inv put_inv"
  and heap_inG[heap_inG_axiom]: "inG get_heap put_heap"
  and prophm_inG[proph_inG_axiom]: "inG get_proph put_proph"
begin

text \<open>Boilerplate setup\<close>
lemmas wp_inG[inG_axioms] = inv_inG heap_inG prophm_inG
abbreviation fancy_upd' ("\<Turnstile>{_,_}=>_") where "fancy_upd' \<equiv> ViewShift.fancy_upd put_inv"
abbreviation wand_fupd' ("_={_,_}=\<^emph>_") where "wand_fupd' \<equiv> ViewShift.wand_fupd put_inv"
abbreviation wand_linear_fupd' ("_={_}=\<^emph>_") where "wand_linear_fupd' \<equiv> ViewShift.wand_linear_fupd put_inv"
abbreviation linear_fupd' ("\<Turnstile>{_}=>_") where "linear_fupd' \<equiv> ViewShift.linear_fupd put_inv"
abbreviation points_to_own' ("_\<mapsto>{#_}_" 60) where "points_to_own' \<equiv> AuthHeap.points_to_own put_heap"
abbreviation points_to_full' (infix "\<mapsto>\<^sub>u" 60) where "points_to_full' \<equiv> AuthHeap.points_to_full put_heap"
abbreviation texan2' ("{{{ _ }}} _ @ _ ; _ {{{ _ }}}") where "texan2' \<equiv> WeakestPrecondition.texan2 put_inv put_heap put_proph"
abbreviation texan' ("{{{ _ }}} _ {{{ _ }}}") where "texan' \<equiv> WeakestPrecondition.texan put_inv put_heap put_proph"
abbreviation WP' ("WP _ {{ _ }}") where "WP e {{ Q }} \<equiv> WeakestPrecondition.WP put_inv put_heap put_proph e Q"
abbreviation atomic_hoare' ("\<langle>_\<rangle>/ _ @ _/ \<langle> _,RET _ \<rangle>") where "atomic_hoare' \<equiv> WeakestPrecondition.atomic_hoare put_inv put_heap put_proph"
abbreviation inv where "inv \<equiv> Invariant.inv put_inv"

lemma cas_atomic_spec: "val_is_unboxed w1 \<Longrightarrow>
  \<langle>\<lambda>v.  l \<mapsto>\<^sub>u v\<rangle> 
    CAS #[l] (Val w1) (Val w2) @ {} 
  \<langle>\<lambda>v _. (if v=w1 then l \<mapsto>\<^sub>u w2 else l \<mapsto>\<^sub>u v),RET \<lambda>v _. #[if v=w1 then True else False]\<rangle>"
  apply (subst atomic_wp_def[OF wp_inG])
  apply brute_force_solver
  apply iwp_bind
  apply (iApply rule: upred_entail_eqL[OF atomic_update_unfold[OF inv_inG]])
  unfolding atomic_acc_def[OF inv_inG]
  apply brute_force_solver
  subgoal
    apply (iWP rule: wp_cmpxchg_success)
    apply (simp add: vals_compare_safe_def)
    apply brute_force_solver
    apply (iApply rule: upred_weakeningR')
    apply iApply_wand
    apply brute_force_solver
    done
  apply (iWP rule: wp_cmpxchg_fail)
  apply (simp add: vals_compare_safe_def)
  apply brute_force_solver
  apply (iApply rule: upred_weakeningR')
  apply iApply_wand
  by brute_force_solver

lift_definition fourth :: frac is "Fract (1::int) (4::int)" by (simp add: zero_less_Fract_iff)
lift_definition three_fourth :: frac is "Fract (3::int) (4::int)" by (simp add: zero_less_Fract_iff)

definition rw_state_inv :: "gname \<Rightarrow> loc \<Rightarrow> (frac \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" where 
  "rw_state_inv \<gamma> l \<Phi> \<equiv> \<exists>\<^sub>u z::int. (l\<mapsto>\<^sub>u#[z]) \<^emph> 
    (((\<upharpoonleft>(z = -1)) \<^emph> own put_rwlock \<gamma> (\<Zspot>A{DfracOwn fourth} {#}))
    \<or>\<^sub>u ((\<upharpoonleft>(0 \<le> z)) \<^emph> (\<exists>\<^sub>u (q::frac) (g:: frac multiset).
      (own put_rwlock \<gamma> (\<Zspot>A g)) \<^emph> (\<upharpoonleft>(int (size g) = z)) \<^emph> (\<upharpoonleft>(fold_mset (+) q g = 1)) \<^emph> \<Phi> q)))"

lemma own_add_split: "(own put_rwlock \<gamma> (\<Zspot>A{DfracOwn(x+y)} a)) \<turnstile> 
  own put_rwlock \<gamma> ((\<Zspot>A{DfracOwn(x)} a) \<cdot> (\<Zspot>A{DfracOwn(y)} a))"
by (auto simp: inG.put_op[OF rwlock_inG, symmetric] op_view_def view_auth_def \<epsilon>_left_id 
  op_option_def op_prod_def op_dfrac_def plus_frac_def op_frac_def to_ag_def op_ag_def Rep_ag_inverse)

lemma auth_valid_multiset_singleton: "valid (\<Zspot>A{dq} g \<cdot> \<circle>A {# v #}) \<Longrightarrow> v \<in># g"
  by (auto simp: valid_def view_auth_def view_frag_def valid_raw_view.rep_eq op_view_def 
    op_option_def n_equiv_ag.rep_eq to_ag.rep_eq \<epsilon>_left_id view_rel_def n_incl_def op_multiset_def 
    \<epsilon>_multiset_def d_equiv)

lemma own_auth_multiset_singleton: "own put_rwlock \<gamma> (\<Zspot>A{dq} g) \<^emph> own put_rwlock \<gamma> (\<circle>A {# v #}) \<turnstile> (\<upharpoonleft>(v\<in>#g))"
  apply iIntro
  apply (iDestruct rule: inG.own_valid2[OF rwlock_inG])
  apply (frule auth_valid_multiset_singleton) by iris_simp

definition rwlock_name :: namespace where "rwlock_name = add_name nroot (string_to_name ''rw_lock'')"
  
definition is_rw_lock :: "gname \<Rightarrow> val \<Rightarrow> (frac \<Rightarrow> 'res upred_f) \<Rightarrow> 'res upred_f" where
  "is_rw_lock \<gamma> lk \<Phi> = (\<triangleright> (internal_fractional \<Phi>)) \<^emph> (\<exists>\<^sub>u l::loc. (\<upharpoonleft>(lk = #[l])) 
    \<^emph> inv rwlock_name (rw_state_inv \<gamma> l \<Phi>))"

lemma [pers_rule, log_prog_rule]: "persistent (is_rw_lock \<gamma> lk \<Phi>)"
  unfolding is_rw_lock_def by log_prog_solver

definition shared_locked :: "gname \<Rightarrow> frac \<Rightarrow> 'res upred_f" where 
  "shared_locked \<gamma> q = own put_rwlock \<gamma> (\<circle>A {# q #})"

definition excl_locked :: "gname \<Rightarrow> 'res upred_f" where
  "excl_locked \<gamma> = own put_rwlock \<gamma> (\<Zspot>A{DfracOwn three_fourth} {#})"

lemma [simp]: "three_fourth + three_fourth > 1"
apply transfer apply auto by (simp add: one_less_Fract_iff)

lemma excl_locked_exclusive: "excl_locked \<gamma> -\<^emph> excl_locked \<gamma> -\<^emph> (\<upharpoonleft>False)"
  unfolding excl_locked_def  
  apply iIntro
  apply (iDestruct rule: inG.own_valid2[OF rwlock_inG])
  by (auto simp: op_view_def view_auth_def op_dfrac_def op_frac.rep_eq op_ag_def op_prod_def 
    op_multiset_def op_option_def valid_def valid_raw_view.rep_eq valid_raw_dfrac.rep_eq valid_raw_frac_def
    three_fourth.rep_eq Fract_le_one_iff)
  
lemma excl_not_shared_locked: "excl_locked \<gamma> -\<^emph> shared_locked \<gamma> q -\<^emph> (\<upharpoonleft>False)"
  unfolding excl_locked_def  shared_locked_def
  apply iIntro
  apply (iDestruct rule: inG.own_valid2[OF rwlock_inG])
  by (auto simp: auth_both_dfrac_n_valid op_prod_def op_multiset_def op_option_def valid_def 
    valid_raw_multiset_def n_incl_def n_equiv_multiset_def)

lemma shared_fraction_not_ge_one: "q\<ge>1 \<Longrightarrow> shared_locked \<gamma> q -\<^emph> rw_state_inv \<gamma> l \<Phi> -\<^emph> (\<upharpoonleft>False)"
apply iIntro
unfolding shared_locked_def rw_state_inv_def
apply iExistsL subgoal for z
apply (rule upred_disjE')
subgoal
  apply iPureL
  apply (check_moveL "own put_rwlock \<gamma> \<circle>A {#q#}")
  apply (iDestruct rule: inG.own_valid2[OF rwlock_inG])
  by (auto simp: valid_def op_view_def view_auth_def view_frag_def op_option_def op_multiset_def
    valid_raw_view.rep_eq view_rel_def valid_raw_dfrac_def valid_raw_frac.rep_eq 
    fourth.rep_eq valid_raw_multiset_def n_incl_def to_ag.rep_eq 
    n_equiv_ag.rep_eq n_equiv_multiset_def)
apply iExistsL+ subgoal for q' g
apply iPureL+
apply (check_move_all True "own put_rwlock \<gamma> \<circle>A {#q#} \<^emph> own put_rwlock \<gamma> \<Zspot>A g")
apply (iDestruct rule: inG.own_valid2[OF rwlock_inG])
apply (auto simp: valid_def op_view_def view_auth_def view_frag_def op_option_def op_multiset_def
    valid_raw_view.rep_eq view_rel_def valid_raw_dfrac_def valid_raw_frac.rep_eq 
    fourth.rep_eq valid_raw_multiset_def n_incl_def to_ag.rep_eq 
    n_equiv_ag.rep_eq n_equiv_multiset_def \<epsilon>_multiset_def)
apply iPureR
by (metis comp_fun_commute.fold_mset_add_mset frac_add_comp_fun_commute frac_sum_one_le leD)
done done

lemma shared_fraction_le_one: 
  "shared_locked \<gamma> q -\<^emph> rw_state_inv \<gamma> l \<Phi> -\<^emph> (\<upharpoonleft>(q<1))"
apply (cases "q<1")
subgoal apply iIntro by iris_simp
apply iIntro apply iris_simp apply (rule shared_fraction_not_ge_one[to_entailment]) 
apply transfer by auto
  
lemma is_rw_lock_iff: "is_rw_lock \<gamma> lk \<Phi> -\<^emph> (\<triangleright>\<box>(\<forall>\<^sub>u q. (\<Phi> q \<longrightarrow>\<^sub>u \<Psi> q) \<and>\<^sub>u (\<Psi> q \<longrightarrow>\<^sub>u \<Phi> q))) -\<^emph> is_rw_lock \<gamma> lk \<Psi>"
  unfolding is_rw_lock_def  
  apply iIntros
  apply (iSplit "?p" "\<triangleright>?p")
  prefer 2 subgoal 
    apply (check_moveL "\<triangleright> (internal_fractional ?p)")
    apply (check_moveL "\<triangleright>\<box>?p")
    apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], unfolded upred_sep_assoc_eq])
    apply (rule upred_later_mono_extR)
    apply (rule upred_entails_trans[OF _ internal_fractional_iff[to_entailment]])
    by iFrame_single+
  subgoal for l
    apply (entails_substR rule: inv_iff[OF inv_inG])  
    apply (iFrame2 "inv ?n ?p")
    apply (check_moveL "\<triangleright> (internal_fractional ?p)")
    apply (check_moveL "\<triangleright>\<box>?p")
    apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], unfolded upred_sep_assoc_eq])
    apply (rule upred_later_mono_extR)
    apply iIntros apply log_prog_solver+
    apply (iDrop "inv ?n ?p") apply (iDrop "internal_fractional ?p")
    apply (rule upred_entails_conjI)
    subgoal
      unfolding rw_state_inv_def
      apply iIntros subgoal for z 
      apply (rule persis_conj_sepL, log_prog_solver)
      apply (iExistsR z)
      apply (iFrame2 "l\<mapsto>\<^sub>u ?x")
      apply (rule upred_disjE')
      subgoal apply (rule upred_disjIL) apply iFrame_single by iPureL
      apply (rule upred_disjIR)
      apply iExistsL+ subgoal for q g apply (iExistsR q, iExistsR g) apply iPureL+ 
      apply (iFrame2 "own ?p ?g ?x")
      apply (iApply rule: upred_persisE) apply (iForallL q) apply (iApply rule: upred_weakeningL')
      apply (check_moveL "\<Phi> q")
      apply (iApply rule: upred_impl_apply') by iFrame_single done done
    unfolding rw_state_inv_def
    apply iIntros subgoal for z 
    apply (rule persis_conj_sepL, log_prog_solver)
    apply (iExistsR z)
    apply (iFrame2 "l\<mapsto>\<^sub>u ?x")
    apply (rule upred_disjE')
    subgoal apply (rule upred_disjIL) apply iFrame_single by iPureL
    apply (rule upred_disjIR)
    apply iExistsL+ subgoal for q g apply (iExistsR q, iExistsR g) apply iPureL+ 
    apply (iFrame2 "own ?p ?g ?x")
    apply (iApply rule: upred_persisE) apply (iForallL q) apply (iApply rule: upred_weakeningR')
    apply (check_moveL "\<Psi> q")
    apply (iApply rule: upred_impl_apply') by iFrame_single done
  done
done 

lemmas auxthm = frame_rule_apply[OF upred_entails_trans[OF fractional_internal_fractional[to_entailment]]]
              
lemma newlock_spec: "as_fractional P \<Phi> 1 \<Longrightarrow>
{{{ P }}}
  newlock $ #[()]
{{{ \<lambda>lk. \<exists>\<^sub>u \<gamma>. is_rw_lock \<gamma> lk \<Phi> }}}"
  apply iIntros subgoal for \<Psi>
  unfolding newlock_def
  apply iwp_beta_later
  apply (rule upred_later_mono_extR)
  apply (rule add_holds[OF inG.own_alloc[OF rwlock_inG, of "\<Zspot>A {#}"]])
  subgoal apply (auto simp: valid_def valid_raw_view.rep_eq view_auth_def view_rel_def 
    n_equiv_ag.rep_eq to_ag.rep_eq d_equiv valid_raw_multiset_def)
    using dcamera_valid_iff valid_dfrac_own by auto
  apply (rule bupd_elim(2), log_prog_solver, fupd_elimL)
  apply (iwp rule: wp_alloc') subgoal for l
  apply (iMod rule: inv_alloc[OF inv_inG, where ?N=rwlock_name and ?P="rw_state_inv \<gamma> l \<Phi>"])
  apply (iApply_wand_as_rule "\<triangleright>?p" "P \<^emph> own put_rwlock \<gamma> \<Zspot>A {#} \<^emph> (l\<mapsto>\<^sub>u ?x)")
  subgoal 
    apply (iApply rule: apply_as_fractional[where ?P=P and ?\<Phi>=\<Phi>])  
    apply iNext 
    unfolding rw_state_inv_def apply (iExistsR 0) apply (iFrame2 "l\<mapsto>\<^sub>u ?x")
    by (iExistsR 1, iExistsR "{#}")
  apply (iwp rule: upred_entail_eqR[OF wp_value_fupd])
  apply fupd_elimL  
  supply is_rw_lock_def[iris_simp] as_fractional_def[iris_simp]
  apply (entails_substR rule: fupd_intro[OF inv_inG])+
  apply (iApply rule: upred_universal_wand)
  apply (iExistsR ?x) apply iFrame_single apply iNext apply auto
  apply (rule auxthm) apply assumption apply (rule upred_entails_refl) apply frame_solver by iris_simp
done done

lemma newlock_spec': "
{{{ emp }}} newlock $ #[()] 
{{{ \<lambda>lk. (\<exists>\<^sub>ul::loc. (\<upharpoonleft>(lk=#[l]))) \<^emph> (\<forall>\<^sub>u P. (((\<upharpoonleft>(as_fractional P Q 1)) \<^emph> P) ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_rw_lock \<gamma> lk Q))) }}}"
  apply iIntros subgoal for \<Psi>
  unfolding newlock_def
  apply iwp_beta_later
  apply (rule upred_later_mono)
  apply (iwp rule: wp_alloc') subgoal for l
  apply iwp_val
  apply (iApply rule: upred_universal_wand)
  apply (iSplit "emp" "upred_exists ?p") prefer 2 apply (iExistsR l)
  apply iIntros subgoal for P
  apply (iApply rule: apply_as_fractional[where ?P=P and ?\<Phi>=Q])
  apply (rule add_holds[OF inG.own_alloc[OF rwlock_inG, of "\<Zspot>A {#}"]])
  subgoal apply (auto simp: valid_def valid_raw_view.rep_eq view_auth_def view_rel_def 
    n_equiv_ag.rep_eq to_ag.rep_eq d_equiv valid_raw_multiset_def)
    using dcamera_valid_iff valid_dfrac_own by auto
  apply (rule bupd_elim(2), log_prog_solver, fupd_elimL)
  subgoal  
  apply (iMod rule: inv_alloc[OF inv_inG, where ?N=rwlock_name and ?P="rw_state_inv \<gamma> l Q"])
  apply (iApply_wand_as_rule "\<triangleright>?p" "Q 1 \<^emph> own put_rwlock \<gamma> \<Zspot>A {#} \<^emph> (l\<mapsto>\<^sub>u ?x)")
  apply iNext 
  apply (subst rw_state_inv_def) apply (iExistsR 0) apply (iFrame2 "l\<mapsto>\<^sub>u ?x")
  apply (iExistsR 1, iExistsR "{#}") apply iFrame_single+
  apply (rule fupd_mono[OF inv_inG])
  apply (iExistsR ?x) apply (subst is_rw_lock_def)
  supply is_rw_lock_def[iris_simp] as_fractional_def[iris_simp]
  apply iFrame_single apply iNext apply auto
  apply (rule auxthm) apply assumption apply (rule upred_entails_refl) apply frame_solver by iris_simp
done done done done
  
lemma try_acquire_shared_spec: "
{{{ is_rw_lock  \<gamma> lk \<Phi> }}}
  try_acquire_shared $ lk
{{{ \<lambda>v. \<exists>\<^sub>ub. (\<upharpoonleft>(v=#[b])) \<^emph> (if b then (\<exists>\<^sub>u q. shared_locked \<gamma> q \<^emph> \<Phi> q \<^emph> (\<upharpoonleft>(q<1))) else emp) }}}"
  unfolding try_acquire_shared_def is_rw_lock_def  
  apply iIntros subgoal for \<Psi> l
  apply iwp_beta
  apply iwp_bind
  apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
    elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver) apply (iDrop "inv ?n ?p")
  apply (subst (2) rw_state_inv_def, iris_simp)
  apply iExistsL subgoal for z
  apply (iwp rule: wp_load_texan) 
  apply (iFrame2 "points_to put_heap l ?d ?x")
  apply (rule upred_later_mono_extR)
  apply iIntros subgoal for v
  apply (rule upred_entails_trans[OF _ frameE[where ?R="\<Turnstile>{UNIV -names rwlock_name}=>(\<triangleright>(rw_state_inv \<gamma> l \<Phi>))"]])
  prefer 2 apply frame_solver apply (rule inv_inG) apply frame_solver
  apply (iSplit "(?p \<or>\<^sub>u ?q) \<^emph> (l\<mapsto>\<^sub>u?x)" "\<Turnstile>{UNIV - names rwlock_name}=>\<triangleright>local.rw_state_inv \<gamma> l \<Phi>")
  prefer 2 subgoal apply (subst (2) rw_state_inv_def) by brute_force_solver
  apply (entails_substR rule: fupd_intro[OF inv_inG])
  apply iwp_beta
  apply (cases "0 \<le> z") prefer 2
  subgoal
    apply iwp_bind
    apply (rule wp_pure[OF wp_inG, of True 1 _ FalseE]) 
      apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
      supply BinOpS[of LeOp "LitV (LitInt 0)" "LitV (LitInt z)", unfolded bin_op_eval_def, simplified, intro]
      apply blast+ using headE(7) apply fastforce apply blast
    apply iwp_val
    apply (iwp_pure_later rule: pure_exec_if_false)
    apply (check_move_all True "(\<triangleright>(internal_fractional ?p))\<^emph>(\<triangleright>(\<forall>\<^sub>u x::val. ?q x))")
    apply (iApply rule: upred_entail_eqR[OF upred_later_sep])
    apply (rule upred_later_mono_extR) 
    apply iterate_hyps apply iterate_hyps by (iExistsR False) 
  apply iwp_bind
  apply (rule wp_pure[OF wp_inG, of True 1 _ TrueE]) 
    apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
    supply BinOpS[of LeOp "LitV (LitInt 0)" "LitV (LitInt z)", unfolded bin_op_eval_def, simplified, intro]
    apply blast+ using headE(7) apply fastforce apply blast
  apply iwp_val
  apply (iwp_pure_later rule: pure_exec_if_true)
  apply (check_move_all True "(\<triangleright>(internal_fractional ?p))\<^emph>(\<triangleright>(\<forall>\<^sub>u x::val. ?q x))")
  apply (iApply rule: upred_entail_eqR[OF upred_later_sep])
  apply (rule upred_later_mono_extR) 
  apply iwp_bind
  apply (rule wp_pure[OF wp_inG, of True 1 _ "Val (LitV (LitInt (z+1)))"])
    apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
    supply BinOpS[of PlusOp "LitV (LitInt z)" "LitV (LitInt 1)", unfolded bin_op_eval_def, simplified, intro]
    apply blast+ using headE(7) apply fastforce apply blast
  apply iwp_val
  apply iwp_bind
  apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
    elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver) apply (iDrop "inv ?n ?p")
  apply (subst (2) rw_state_inv_def) apply iris_simp apply iIntros subgoal for z'
  apply (split_moveO "\<triangleright>l\<mapsto>\<^sub>u?x")
  apply (cases "z=z'"; iris_simp) prefer 2
  subgoal
    apply (iwp rule: wp_cmpxchg_fail2, auto simp: vals_compare_safe_def) apply iNext
    apply iwp_val
    apply (entails_substR rule: fupd_intro[OF inv_inG])
    apply (check_moveL "\<triangleright>?P")
    apply (iSplit "(\<triangleright>?P) \<^emph> (l\<mapsto>\<^sub>u ?x)" "\<triangleright>?q") prefer 2
    subgoal apply (rule upred_later_mono_extR) apply (subst (2) rw_state_inv_def)
      apply (iExistsR "z'") by iFrame_single+   
    apply (iwp_pure rule: pure_exec_snd)
    apply iwp_val apply (iApply rule: upred_universal_wand) by (iExistsR "False")
  apply (iwp rule: wp_cmpxchg_suc, auto simp: vals_compare_safe_def)
  apply iIntros subgoal for q g
  apply (rule upred_later_mono_extR, iris_simp)
  apply (subst (10) half_frac_eq)
  apply (iApply_step2 "\<Phi> (half q) \<^emph> \<Phi> (half q)" "\<Phi> ?x \<^emph> internal_fractional \<Phi>")
  subgoal unfolding internal_fractional_def apply (iApply rule: upred_persisE)
    apply (iForallL "half q", iForallL "half q") apply (iApply rule: upred_weakeningL') 
    apply iApply_wand by iFrame_single+
  apply iwp_val
  apply (iApply rule: inG.own_update[OF rwlock_inG, where ?b = "\<Zspot>A (g + {# half q #}) \<cdot> \<circle>A {# half q #}"])
  subgoal apply (rule put_update[OF rwlock_inG])
    apply (subst \<epsilon>_multiset_def[symmetric])
    apply (rule auth_update_alloc)
    by (rule multiset_local_update_alloc[where ?x'="{#half q#}", simplified])
  apply (rule bupd_elim(2)[OF inv_inG])
  apply (rule fupd_frame_mono[OF inv_inG])
  apply iPureL+
  apply (iApply rule: upred_entail_eqL[OF inG.own_op[OF rwlock_inG]]) 
  apply (rule split_frame) prefer 2 apply (rule can_be_split_refl)
  apply (rule can_be_split_sepR) apply (rule can_be_split_sepL)
  apply (rule can_be_split_sepL) apply (rule persistent_dupl_split', log_prog_solver)
  apply (rule can_be_split_sepR) apply (rule persistent_dupl_split', log_prog_solver)
  apply (rule can_be_split_refl)
  subgoal apply iNext apply (subst (2) rw_state_inv_def) apply (iExistsR "z'+1")
    apply (iFrame2 "l\<mapsto>\<^sub>u?x") apply (iExistsR "?x")+ apply (iFrame2 "own put_rwlock \<gamma> ?x")
    apply (iFrame2 "\<Phi> ?x") apply iPureR
    unfolding comp_fun_commute.fold_mset_add_mset[OF frac_add_comp_fun_commute]
    comp_fun_commute.fold_mset_fun_left_comm[OF frac_add_comp_fun_commute]
    half_frac_eq[symmetric] by assumption
  apply (iwp_pure rule: pure_exec_snd)
  apply iwp_val
  apply (iApply rule: upred_universal_wand[where ?'b=val])
  apply (iExistsR True) apply (iExistsR "half q")
  unfolding shared_locked_def apply iFrame_single
  subgoal by (metis comp_fun_commute.fold_mset_fun_left_comm frac_add_comp_fun_commute frac_sum_one_le half_frac_eq)
  by iFrame_single+
done done done done done

lemma acquire_shared_spec:"
{{{ is_rw_lock \<gamma> lk \<Phi> }}}
  acquire_shared $ lk
{{{ \<lambda>_. \<exists>\<^sub>u q. shared_locked \<gamma> q \<^emph> \<Phi> q \<^emph> (\<upharpoonleft>(q<1)) }}}"
  apply iIntros
  apply (rule upred_wandE) apply (rule persistent_loebI, log_prog_solver) apply iIntro
  unfolding acquire_shared_def
  apply (iApply rule: upred_entail_eqL[OF upred_persis_later]) apply (iDrop "\<box> ?P")+
  apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], simplified iris_simp])
  apply brute_force_solver
  apply iwp_bind
  apply (iwp rule: try_acquire_shared_spec)
  apply (iFrame2 "is_rw_lock ?g ?l ?q") apply iNext apply iIntros apply auto
  apply iIntros apply (iwp_pure_later rule: pure_exec_if_true) apply brute_force_solver
  apply iIntros apply (iwp_pure rule: pure_exec_if_false) 
  apply (iApply rule: upred_persisE) apply (iDrop "\<box>?x") apply iApply_wand by iFrame_single

lemma mset_in_emp: "q \<in># g \<Longrightarrow> g\<noteq>{#}" by auto
  
lemma release_shared_spec:"
{{{ is_rw_lock \<gamma> lk \<Phi> \<^emph> shared_locked \<gamma> q \<^emph> \<Phi> q }}}
  release_shared $ lk
{{{ \<lambda>_. emp }}}"
  unfolding release_shared_def
  apply iIntros
  unfolding is_rw_lock_def
  apply (check_moveL "upred_exists (?P::loc \<Rightarrow> 'res upred_f)") apply iIntros
  apply iwp_beta
  apply iwp_seq
  apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
    elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver) apply (iDrop "inv ?n ?p")
  apply (subst (2) rw_state_inv_def, iris_simp) apply iExistsL subgoal for \<phi> l z
  apply (split_moveO "\<triangleright> l\<mapsto>\<^sub>u?x")
  apply (iwp rule: wp_faa)
  apply (iFrame2 "l\<mapsto>\<^sub>u?x")
  apply (check_move_all True "(\<triangleright>(internal_fractional \<Phi>))\<^emph>\<triangleright>(upred_forall (?x::val\<Rightarrow>'res upred_f))")
  apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], simplified iris_simp])+
  apply (rule upred_later_mono_extR)
  apply iIntros
  apply (check_moveL "?p\<or>\<^sub>u?q")
  apply (rule upred_disjE') unfolding shared_locked_def 
  subgoal apply iIntros 
    apply (check_moveL "own put_rwlock \<gamma> \<circle>A {#q#}")
    apply (iDestruct rule: inG.own_valid2[OF rwlock_inG])
    by (auto simp: valid_def op_view_def view_auth_def view_frag_def valid_raw_view.rep_eq 
      op_option_def view_rel_def \<epsilon>_left_id n_incl_def op_multiset_def to_ag.rep_eq n_equiv_ag.rep_eq
      n_equiv_multiset_def)
  apply iIntros apply auto subgoal for q' g
  apply (iAssert_pers "\<upharpoonleft>(0<z \<and> q \<in>#g)") subgoal
    apply (check_moveL "own put_rwlock \<gamma> \<circle>A {#q#}")
    apply (check_moveL "own put_rwlock \<gamma> \<Zspot>A g")
    apply (iDestruct rule: inG.own_valid2[OF rwlock_inG])
    apply iPureR
    by (auto simp: valid_def op_view_def view_auth_def view_frag_def valid_raw_view.rep_eq 
      op_option_def view_rel_def \<epsilon>_left_id n_incl_def op_multiset_def to_ag.rep_eq n_equiv_ag.rep_eq
      n_equiv_multiset_def)
  apply iPureL
  apply (check_moveL "own put_rwlock \<gamma> \<circle>A {#q#}")
  apply (check_moveL "own put_rwlock \<gamma> \<Zspot>A g")
  apply (iApply rule: upred_entail_eqR[OF inG.own_op[OF rwlock_inG]])
  apply (iApply rule: inG.own_update[OF rwlock_inG, where ?b = "\<Zspot>A (g - {# q #})"])
  subgoal apply (rule put_update[OF rwlock_inG])   
    apply (subst camera_comm)
    apply (rule auth_update_dealloc)
    apply (subst \<epsilon>_multiset_def)
    apply (subst (3) Multiset.diff_cancel[symmetric, of "{#q#}"])
    apply (rule multiset_local_update_dealloc)
    by simp
  apply (rule bupd_elim(2)[OF inv_inG])
  apply (rule fupd_frame_mono[OF inv_inG])
  apply (iSplitR "\<forall>\<^sub>uv. emp -\<^emph> \<phi> v" "WP' ?x ?y")
  subgoal apply iwp_beta by brute_force_solver
  apply iNext apply (subst (2) rw_state_inv_def) apply (iExistsR "z-1")
  apply (iFrame2 "l\<mapsto>\<^sub>u?x")
  apply auto
  apply (frule mset_in_emp, iris_simp)
  apply (iExistsR ?x) apply (iFrame2 "own put_rwlock ?g ?x")
  apply (iApply_step2 "\<Phi> (q + q')" "\<Phi> q \<^emph> \<Phi> q'")
  subgoal unfolding internal_fractional_def apply (iApply rule: upred_persisE)
    apply (iForallL q, iForallL "q'") apply (iApply rule: upred_weakeningR') 
    apply (check_moveL "\<Phi> q", check_moveL "\<Phi> q'", check_moveL "?p-\<^emph>?q") 
    apply (entails_substL rule: upred_wand_apply[of "\<Phi> q \<^emph> \<Phi> q'"]) by iFrame_single
  apply iFrame_single
  apply iPureR
  apply (metis add_mset_remove_trivial_eq comp_fun_commute.fold_mset_add_mset comp_fun_commute.fold_mset_fun_left_comm frac_add_comp_fun_commute)
  apply iPureR by (simp add: size_Diff_singleton_if)
  using valid_dfrac_own by blast
done

lemma try_acquire_excl_spec:"
{{{ is_rw_lock \<gamma> lk \<Phi> }}}
  try_acquire_excl $ lk
{{{ \<lambda>v. \<exists>\<^sub>ub. (\<upharpoonleft>(v=#[b])) \<^emph> (if b then excl_locked \<gamma> \<^emph> \<Phi> 1 else emp) }}}"
apply iIntros
unfolding try_acquire_excl_def
apply iwp_beta
apply iwp_bind
unfolding is_rw_lock_def apply iIntros
apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
    elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver) apply (iDrop "inv ?n ?p")
apply (subst (2) rw_state_inv_def, iris_simp) apply iExistsL subgoal for \<phi> l z
apply (split_moveO "\<triangleright>l\<mapsto>\<^sub>u?x")
apply (cases "z=0", auto simp: iris_simp) prefer 2
subgoal
  apply (iwp rule: wp_cmpxchg_fail2, auto simp: vals_compare_safe_def)
  apply (check_move_all True "(\<triangleright>(internal_fractional \<Phi>))\<^emph>(\<triangleright>(upred_forall (?x::val\<Rightarrow>'res upred_f))) 
      \<^emph> \<triangleright>(?p\<or>\<^sub>u?q)")
  apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], simplified iris_simp])+
  apply brute_force_solver
  apply (iSplitR "upred_forall ?x" "WP' ?y ?z")
  subgoal apply (iwp_pure rule: pure_exec_snd) apply iwp_val 
    apply (iApply rule: upred_universal_wand) by (iExistsR False)
    apply iNext apply (subst (2) rw_state_inv_def) apply (iExistsR z) by iFrame_single+
apply (iwp rule: wp_cmpxchg_suc, auto simp: vals_compare_safe_def)
apply iIntros
apply (check_move_all True "(\<triangleright>(internal_fractional \<Phi>))\<^emph>(\<triangleright>(upred_forall (?x::val\<Rightarrow>'res upred_f)))")
apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], simplified iris_simp])+
apply (rule upred_later_mono_extR)
apply brute_force_solver
apply (subst unfold_add_view[of "fourth" "three_fourth"])
subgoal apply transfer by (auto simp: One_rat_def eq_rat(1))
apply (iApply rule: own_add_split) apply (iApply rule: upred_entail_eqL[OF inG.own_op[OF rwlock_inG]])
apply (iSplit "l\<mapsto>\<^sub>u?x\<^emph>own put_rwlock \<gamma> \<Zspot>A{DfracOwn fourth} {#}" "\<triangleright>?p")
subgoal unfolding excl_locked_def apply (iwp_pure rule: pure_exec_snd) 
  apply iwp_val apply (iApply rule: upred_universal_wand) apply (iExistsR True)
  by iFrame_single+
apply iNext apply (subst (2) rw_state_inv_def) apply (iExistsR "-1") by iFrame_single+
done

lemma acquire_excl_spec:"
{{{ is_rw_lock \<gamma> lk \<Phi> }}}
  acquire_excl $ lk
{{{ \<lambda>_. excl_locked \<gamma> \<^emph> \<Phi> 1 }}}"
apply iIntros
apply (rule upred_wandE) apply (rule persistent_loebI, log_prog_solver) apply iIntro
apply (iApply rule: upred_entail_eqL[OF upred_persis_later]) apply (iDrop "\<box> ?P")+
apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], simplified iris_simp])
unfolding acquire_excl_def
apply brute_force_solver
apply iwp_bind
apply (iwp rule: try_acquire_excl_spec)
apply (iFrame2 "is_rw_lock ?g ?l ?p")
apply iNext apply (iIntros, auto)+
subgoal for \<phi> b apply (iwp_pure_later rule: pure_exec_if_true) by brute_force_solver
apply iIntros
apply (iwp_pure rule: pure_exec_if_false) 
by (iApply rule: upred_persisE,iApply_wand,iFrame_single)

lemma release_excl_spec:"
{{{ is_rw_lock \<gamma> lk \<Phi> \<^emph> excl_locked \<gamma> \<^emph> \<Phi> 1 }}}
  release_excl $ lk
{{{ \<lambda>_. emp }}}"
apply iIntros
unfolding is_rw_lock_def release_excl_def
apply (check_moveL "upred_exists (?x::loc \<Rightarrow> _)")
apply iIntros
apply iwp_beta
apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] 
    elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp], atomic_solver) apply (iDrop "inv ?n ?p")
apply (subst (2) rw_state_inv_def, iris_simp) apply iExistsL subgoal for \<phi> l z
apply (split_moveO "\<triangleright>l\<mapsto>\<^sub>u?x")
apply (iwp rule: wp_store_texan)
apply (iFrame2 "l\<mapsto>\<^sub>u?x")
apply (check_move_all True "(\<triangleright>(internal_fractional \<Phi>))\<^emph>(\<triangleright>(upred_forall (?x::val\<Rightarrow>'res upred_f))) 
      \<^emph> \<triangleright>(?p\<or>\<^sub>u?q)")
apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], simplified iris_simp])+
apply brute_force_solver
apply (subst (2) rw_state_inv_def) unfolding excl_locked_def
apply (iSplitR "\<forall>\<^sub>uv. emp -\<^emph> \<phi> v" "\<phi> ?x") apply brute_force_solver+
apply (rule upred_disjE')
subgoal apply iIntros
  apply (check_moveL "own put_rwlock \<gamma> \<Zspot>A{DfracOwn three_fourth} {#}", iris_simp)
  apply (iDestruct rule: upred_entail_eqR[OF inG.own_op[OF rwlock_inG]])
  apply (auto simp: op_view_def view_auth_def op_option_def \<epsilon>_left_id op_prod_def op_dfrac_def 
    op_frac_def fourth.rep_eq three_fourth.rep_eq op_ag_def to_ag_def Rep_ag_inverse One_rat_def 
    one_frac_def eq_rat(1))
  by (metis (no_types, opaque_lifting) Fract_add_one One_rat_def add.commute add.right_neutral 
    rat_number_collapse(1) upred_weakeningR zero_neq_numeral)
apply iIntros
apply (iDrop "\<Phi> ?x")  
apply (check_moveL "own put_rwlock \<gamma> \<Zspot>A{DfracOwn three_fourth} {#}")
apply (iDestruct rule: inG.own_valid2[OF rwlock_inG])
apply (auto simp: valid_def op_view_def view_auth_def valid_raw_view.rep_eq op_option_def 
  op_prod_def op_dfrac_def valid_raw_dfrac_def)
using frac_not_valid[unfolded valid_def] by blast
done
end
end