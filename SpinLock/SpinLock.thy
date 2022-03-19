theory SpinLock
imports "../SpanningTree/Spanning"
begin

definition newlock :: val where "newlock \<equiv>
  V\<lambda> None: Ref FalseE"
definition acquire :: val where "acquire \<equiv>
  rec: (Some ''acquire'') (Some ''l'') :=
    if: CAS (V ''l'') FalseE TrueE then #[()]
    else App (V ''acquire'') (V ''l'') endif"
definition release :: val where "release \<equiv>
  V\<lambda> (Some ''l''): ((V ''l'') \<leftarrow> FalseE)"

definition "lock_name :: gname \<equiv> 7"
definition lockN :: namespace where "lockN \<equiv> add_name nroot (string_to_name ''spin_lock'')"

definition lock_inv :: "gname \<Rightarrow> loc \<Rightarrow> iprop \<Rightarrow> iprop" where
  "lock_inv \<gamma> l R \<equiv> \<exists>\<^sub>u b. l\<mapsto>\<^sub>u#[b] \<^emph> (\<upharpoonleft>b \<or>\<^sub>u (\<upharpoonleft>(\<not>b) \<^emph> Own (constr_lock \<gamma> (Ex ())) \<^emph> R))"

definition is_lock :: "gname \<Rightarrow> val \<Rightarrow> iprop \<Rightarrow> iprop" where
  "is_lock \<gamma> lk R \<equiv> \<exists>\<^sub>u l. \<upharpoonleft>(lk=#[l]) \<and>\<^sub>u inv lockN (lock_inv \<gamma> l R)"

definition "locked \<gamma> \<equiv> Own (constr_lock \<gamma> (Ex ()))"

lemma is_lock_pers [pers_rule, log_prog_rule]: "persistent (is_lock \<gamma> lk R)" 
  unfolding is_lock_def by (log_prog_solver)

lemma lock_alloc: "\<exists>\<^sub>u \<gamma>.\<Rrightarrow>\<^sub>b (locked \<gamma>)"
  apply iIntro
  apply (iExistsR "0::nat")
  unfolding locked_def
  apply (entails_substR rule: rule: own_alloc)
  by (auto simp: valid_def constr_lock_def prod_n_valid_def \<epsilon>_n_valid valid_raw_ex_def)

context wp_rules begin
lemma newlock_spec:
  "{{ upred_emp }} App newlock #[()] {{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}"
  \<comment> \<open>Unfold newlock definition\<close>
  apply (auto simp: newlock_def subst'_def intro!: wp_pure[OF pure_exec_beta])
  \<comment> \<open>Remove wp based on wp_alloc.\<close>
  apply (iApply rule: wp_alloc, remove_emp)
  apply (iDestruct rule: wp_mono)
  \<comment> \<open>Allocate lock and lock_inv.\<close>
  apply (rule upred_forallI, rule upred_wandI)
  apply (rule add_holds[OF lock_alloc])
  apply iExistsL subgoal for v l R \<gamma>
  apply (iMod rule: upd_fupd)
  apply (iApply_step "?P" rule: inv_alloc[of "lock_inv _ _ R" _ lockN])
  unfolding lock_inv_def
  apply (entails_substR rule: upred_laterI)
  apply (iExistsR False, simp)
  apply (iFrame2 "?l\<mapsto>\<^sub>uFalseV\<^emph>R", simp add: locked_def emp_rule)
  apply (rule upred_entails_refl)
  \<comment> \<open>Cleanup\<close>
  apply (rule fupd_mono)
  unfolding is_lock_def lock_inv_def[symmetric]
  apply (iExistsR \<gamma>)
  apply (iExistsR l)
  apply (rule upred_entails_conjI)
  by auto done
end
end