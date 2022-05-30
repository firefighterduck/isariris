theory Demo
imports DemoSetup
begin

text \<open>Spin lock implementation\<close>
definition newlock :: val where "newlock \<equiv>
  V\<lambda> None: Ref FalseE"
  
definition acquire :: val where "acquire \<equiv>
  rec: (Some ''acquire'') (Some ''l'') :=
    if: CAS (V ''l'') FalseE TrueE then #[()]
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
  and heap_inG[heap_inG_axiom]: "inG get_heap put_heap"
  and inv_inG[inv_inG_axiom]: "inG get_inv put_inv"
  and prophm_inG[proph_inG_axiom]: "inG get_proph put_proph"
begin

text \<open>Boilerplate setup\<close>
lemmas wp_inG[inG_axioms] = inv_inG heap_inG prophm_inG
abbreviation fancy_upd ("\<Turnstile>{_,_}=>_") where "fancy_upd \<equiv> ViewShift.fancy_upd put_inv"
abbreviation wand_fupd ("_={_,_}=\<^emph>_") where "wand_fupd \<equiv> ViewShift.wand_fupd put_inv"
abbreviation wand_linear_fupd ("_={_}=\<^emph>_") where "wand_linear_fupd \<equiv> ViewShift.wand_linear_fupd put_inv"
abbreviation linear_fupd ("\<Turnstile>{_}=>_") where "linear_fupd \<equiv> ViewShift.linear_fupd put_inv"
abbreviation points_to_own ("_\<mapsto>{#_}_" 60) where "points_to_own \<equiv> AuthHeap.points_to_own put_heap"
abbreviation points_to_full (infix "\<mapsto>\<^sub>u" 60) where "points_to_full \<equiv> AuthHeap.points_to_full put_heap"
abbreviation texan2 ("{{{ _ }}} _ @ _ ; _ {{{ _ }}}") where "texan2 \<equiv> WeakestPrecondition.texan2 put_inv put_heap put_proph"
abbreviation texan ("{{{ _ }}} _ {{{ _ }}}") where "texan \<equiv> WeakestPrecondition.texan put_inv put_heap put_proph"
abbreviation WP ("WP _ {{ _ }}") where "WP e {{ Q }} \<equiv> WeakestPrecondition.WP put_inv put_heap put_proph e Q"
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
  by (auto simp: valid_def constr_lock_def prod_n_valid_def \<epsilon>_n_valid valid_raw_ex_def)
  
declare frame_rule_apply[OF upred_entails_trans[OF upred_entails_trans[OF lock_alloc[to_entailment] 
  upred_exist_mono[OF upd_fupd[to_entailment]]] fupd_exists_lift[OF inv_inG]], alloc_rule]
lemmas [iris_simp] = lock_inv_def is_lock_def newlock_def acquire_def release_def

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
  "{{{ upred_emp }}} App newlock #[()] {{{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}}"
  by brute_force_solver
  
lemma release_spec: 
  "{{{ is_lock \<gamma> lk R \<^emph> locked \<gamma> \<^emph> R }}} App release lk {{{ \<lambda>_. upred_emp }}}"
  by brute_force_solver
end
end