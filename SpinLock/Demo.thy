theory Demo
imports DemoSetup
begin

text \<open>Spin lock implementation\<close>
definition newlock :: val where "newlock \<equiv>
  V\<lambda> None: Ref FalseE"

definition try_acquire :: val where "try_acquire \<equiv>
  V\<lambda> Some ''l'': CAS (V ''l'') FalseE TrueE"
  
definition acquire :: val where "acquire \<equiv>
  rec: (Some ''acquire'') (Some ''l'') :=
    if: App try_acquire (V ''l'') then #[()]
    else App (V ''acquire'') (V ''l'') endif"

definition release :: val where "release \<equiv>
  V\<lambda> (Some ''l''): ((V ''l'') \<leftarrow> FalseE)"
 
context 
fixes get_lock :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> lockG option"
  and put_lock
  and get_heap :: "gname \<Rightarrow> 'res \<Rightarrow> heap_lang_heap option"
  and put_heap
  and get_inv :: "gname \<Rightarrow> 'res \<Rightarrow> inv option"
  and put_inv
  and get_proph :: "gname \<Rightarrow> 'res \<Rightarrow> (proph_id, val\<times>val) proph_mapGS option"
  and put_proph
assumes lock_inG[lock_inG_axiom]: "inG get_lock put_lock"
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

text \<open>Auxiliary predicates\<close>
definition locked :: "gname \<Rightarrow> 'res upred_f" where
  "locked \<gamma> = own put_lock \<gamma> (Ex ())"

definition lock_inv :: "gname \<Rightarrow> loc \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" where
  "lock_inv \<gamma> l R \<equiv> \<exists>\<^sub>u b. l\<mapsto>\<^sub>u#[b] \<^emph> ((\<upharpoonleft>b) \<or>\<^sub>u ((\<upharpoonleft>(\<not>b)) \<^emph> (locked \<gamma>) \<^emph> R))"

definition lockN :: namespace where "lockN \<equiv> add_name nroot (string_to_name ''spin_lock'')"  
definition is_lock :: "gname \<Rightarrow> val \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" where
  "is_lock \<gamma> lk R \<equiv> \<exists>\<^sub>u l. (\<upharpoonleft>(lk=#[l])) \<and>\<^sub>u inv lockN (lock_inv \<gamma> l R)"

lemma lock_alloc: "\<exists>\<^sub>u \<gamma>.\<Rrightarrow>\<^sub>b (locked \<gamma>)"
  apply iIntro
  apply (iExistsR "0::nat")
  unfolding locked_def
  apply (entails_substR rule: inG.own_alloc[OF lock_inG])
  by (auto simp: valid_def upd_lock_def prod_n_valid_def \<epsilon>_n_valid valid_raw_ex_def)
  
declare frame_rule_apply[OF upred_entails_trans[OF upred_entails_trans[OF lock_alloc[to_entailment] 
  upred_exist_mono[OF upd_fupd[to_entailment]]] fupd_exists_lift[OF inv_inG]], alloc_rule]
lemmas [iris_simp] = lock_inv_def is_lock_def newlock_def acquire_def release_def try_acquire_def

text \<open>Specification\<close>
lemma newlock_spec:
  "{{{ emp }}} App newlock #[()] {{{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}}"
  \<comment> \<open>Reduce the hoare tripple.\<close>
  apply iIntro
  apply (entails_substR rule: upred_persis_mono[where ?P=upred_emp, unfolded emp_rule])
  apply iForallR
  apply (rule upred_wandI)+
  apply iris_simp
  \<comment> \<open>Symbolically execute the call of \<^term>\<open>newlock\<close>.\<close>
  apply (entails_substR rule: wp_pure_step_later[OF wp_inG pure_exec_beta, simplified])
  apply iris_simp
  apply (rule upred_later_mono)
  \<comment> \<open>Symbolically execute the allocation of the heap cell for the lock.\<close>
  apply (iWP rule: wp_alloc')
  apply (entails_substR rule: wp_value[OF wp_inG])
  \<comment> \<open>Use form of entailment to reduce reasoning further.\<close>
  apply (iApply rule: upred_universal_wand)
  apply iForallR
  apply (rule upred_wandI)
  \<comment> \<open>Deallocate invariant on goal side.\<close>
  apply allocate
  apply (move_sepL "?l\<mapsto>\<^sub>u?f")
  apply framing
  \<comment> \<open>Deallocate the locked ghost predicate.\<close>
  apply allocate
  apply (iMod rule: fupd_intro[OF inv_inG])
  apply (rule upred_laterI)
  oops
  
lemma newlock_spec:
  "{{{ emp }}} App newlock #[()] {{{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}}"
  by brute_force_solver
  
lemma release_spec: 
  "{{{ is_lock \<gamma> lk R \<^emph> locked \<gamma> \<^emph> R }}} App release lk {{{ \<lambda>_. upred_emp }}}"
  by brute_force_solver

thm upred_entails_trans[OF _ wp_pure_step_later[OF _ _ _ pure_exec_beta, simplified]]
lemma if_to_ectxt: "if: v then e1 else e2 endif = lang_ctxt (FI (IfCtx e1 e2)) v"
  by auto

lemma cas_atomic_spec: "val_is_unboxed w1 \<Longrightarrow>
  \<langle>\<lambda>v.  l \<mapsto>\<^sub>u v\<rangle> 
    CAS #[l] (Val w1) (Val w2) @ {} 
  \<langle>\<lambda>v _. (if v=w1 then l \<mapsto>\<^sub>u w2 else l \<mapsto>\<^sub>u v),RET \<lambda>v _. #[if v=w1 then True else False]\<rangle>"
  apply (subst atomic_wp_def[OF wp_inG])
  apply brute_force_solver
  apply (entails_substR rule: wp_bind'[OF wp_inG, where C = Snd])
  apply (iApply rule: upred_entail_eqL[OF atomic_update_unfold[OF inv_inG]])
  unfolding atomic_acc_def[OF inv_inG]
  apply brute_force_solver
  subgoal
    apply (iWP rule: wp_cmpxchg_success)
    apply (simp add: vals_compare_safe_def)
    apply brute_force_solver
    apply (iApply rule: upred_weakeningR')
    apply iApply_wand
    apply brute_force_solver done
  apply (iWP rule: wp_cmpxchg_fail)
  apply (simp add: vals_compare_safe_def)
  apply brute_force_solver
  apply (iApply rule: upred_weakeningR')
  apply iApply_wand
  by brute_force_solver

lemma ignore_wand: "P \<turnstile> X \<^emph> Q \<Longrightarrow> P \<^emph> (Q -\<^emph> R) \<turnstile> X"
apply transfer
apply auto
by (meson n_incl_def order_refl)
  
lemma try_acquire_spec: "{{{ is_lock \<gamma> lk R }}} 
    App try_acquire lk
  {{{\<lambda>v. \<exists>\<^sub>ub. (\<upharpoonleft>(v=#[b])) \<^emph> (if b then locked \<gamma> \<^emph> R else emp) }}}"
  apply brute_force_solver
  apply (entails_substR rule: wp_bind'[OF wp_inG, where C = Snd])
  apply (iApply rule: elim_inv_applied'[OF elim_inv_elim_acc[OF inv_into_acc[OF inv_inG] elim_acc_wp_atomic[OF wp_inG]], simplified iris_simp])
  apply atomic_solver
  apply (iDrop "inv ?n ?p")
  apply iExistsL subgoal for \<Phi> l b apply (cases b)
  subgoal
    apply iris_simp
    apply (rule wp_cmpxchg_fail2[simplified, where ?l = l, OF wp_inG], auto simp: vals_compare_safe_def)
    apply iNext
    apply (entails_substR rule: wp_value[OF wp_inG])
    apply (entails_substR rule: fupd_intro[OF inv_inG])
    apply (iExistsR True)
    apply (entails_substR rule: upred_laterI)
    apply iFrame_single
    apply (iWP rule: wp_pure[OF _ _ _ pure_exec_snd]) apply (iDrop "inv ?n ?p")
    apply (entails_substR rule: wp_value[OF wp_inG])
    apply (iApply rule: upred_universal_wand)
    by (iExistsR False)
  apply iris_simp
  apply (split_move "l\<mapsto>\<^sub>uFalseV")
  apply (rule wp_cmpxchg_suc[simplified, where ?l = l, OF wp_inG], auto simp: vals_compare_safe_def)
  apply (check_moveL "\<triangleright>?P") apply (rule upred_later_mono_extR, iris_simp)
  apply (entails_substR rule: wp_value[OF wp_inG])
  apply (entails_substR rule: fupd_intro[OF inv_inG])
  apply (iExistsR True)
  apply (entails_substR rule: upred_laterI)
  apply iFrame_single
  apply (iWP rule: wp_pure[OF _ _ _ pure_exec_snd]) apply (iDrop "inv ?n ?p")
  apply (entails_substR rule: wp_value[OF wp_inG])
  apply (check_moveL "upred_forall (?P::val\<Rightarrow>_)")
  apply (iApply rule: upred_universal_wand)
  by (iExistsR True)
  done
  
lemma acquire_spec:
  "{{{ is_lock \<gamma> lk R }}} App acquire lk {{{ \<lambda>_. locked \<gamma> \<^emph> R }}}"
  apply iIntro
  apply (rule persistent_persisI,pers_solver)
  supply try_acquire_def[iris_simp del]
  apply iForallR subgoal for \<Phi>
  apply (rule upred_wandI)
  apply (entails_substR rule: loeb_useful)
  apply iIntros apply (rule inv_inG)
  subgoal for l
  apply iIntros
  apply (iApply rule: upred_entail_eqL[OF upred_persis_later]) apply (iDrop "\<box> ?P")+
  apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], simplified iris_simp])
  apply (entails_substR rule: wp_pure_step_later[OF wp_inG pure_exec_beta, simplified])
  apply brute_force_solver
  apply (subst (2) if_to_ectxt)
  apply (entails_substR rule: wp_bind[OF wp_inG])
  apply (entails_substR rule: texan_apply[OF wp_inG try_acquire_spec[of \<gamma> _ R]])
  apply brute_force_solver
  subgoal
    apply (rule wp_pure[OF wp_inG pure_exec_if_true], simp)
    apply (entails_substR rule: wp_value[OF wp_inG])
    apply (iApply rule: upred_universal_wand[where ?'b=val])
    by frame_single+
  apply (rule wp_pure[OF wp_inG pure_exec_if_false], simp)
  using upred_wand_apply'
  apply (iApply rule: upred_persisE)
  by (rule upred_laterI)
  done done
end
end