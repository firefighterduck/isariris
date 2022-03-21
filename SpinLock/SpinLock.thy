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

lemma locked_timeless [timeless_rule, log_prog_rule]: "timeless (locked \<gamma>)"
  by (auto simp: constr_lock_def locked_def intro!: log_prog_rule)

lemma lock_alloc: "\<exists>\<^sub>u \<gamma>.\<Rrightarrow>\<^sub>b (locked \<gamma>)"
  apply iIntro
  apply (iExistsR "0::nat")
  unfolding locked_def
  apply (entails_substR rule: rule: own_alloc)
  by (auto simp: valid_def constr_lock_def prod_n_valid_def \<epsilon>_n_valid valid_raw_ex_def)

lemmas [iris_simp] = lock_inv_def locked_def is_lock_def newlock_def
  
context wp_rules begin
lemma newlock_spec:
  "{{ upred_emp }} App newlock #[()] {{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}"
  \<comment> \<open>Unfold newlock definition\<close>
  apply (auto simp: newlock_def subst'_def intro!: wp_pure[OF pure_exec_beta])
  \<comment> \<open>Remove wp based on wp_alloc.\<close>
  apply (iApply rule: wp_alloc)
  apply (iDestruct rule: wp_mono)
  \<comment> \<open>Allocate lock and lock_inv.\<close>
  apply (rule upred_forallI, rule upred_wandI)
  apply (rule add_holds[OF lock_alloc])
  apply iExistsL subgoal for v l R \<gamma>
  apply (iMod rule: upd_fupd)
  apply (iApply_step "?P" rule: inv_alloc[of "lock_inv _ _ R" _ lockN])
  apply (entails_substR rule: upred_laterI)
  apply (iExistsR False)
  apply (iFrame2 "?l\<mapsto>\<^sub>uFalseV\<^emph>R")
  apply (rule upred_entails_refl)
  \<comment> \<open>Cleanup\<close>
  apply (rule fupd_mono)
  apply (iExistsR \<gamma>)
  by (iExistsR l)
  oops

lemmas newlock_intros[intro] = wp_pure[OF pure_exec_beta] upred_entails_trans[OF wp_alloc[to_entailment]] 
    wp_mono upred_forallI upred_wandI upred_existsE'
    upred_entails_substE[OF upd_fupd[to_entailment]] elim_modal_entails'[OF elim_modal_fupd]
    elim_modal_entails[OF elim_modal_timeless'] elim_modal_entails'[OF elim_modal_timeless']
    upred_entails_trans[OF upred_wand_apply'] upred_entails_trans[OF _ upred_laterI] log_prog_rule
    upred_existsI upred_pure_impl upred_pure_impl' upred_pureI upred_pureI' upred_entails_refl 
    upred_weakeningR upred_weakeningL fupd_mono upred_entails_conjI  
    framing' can_be_split_refl can_be_split_baseR can_be_split_sepL

lemma move_pure: "(\<upharpoonleft>b) \<^emph> P = P \<^emph> \<upharpoonleft>b" "P \<^emph> (\<upharpoonleft>b) \<^emph> Q = P \<^emph> Q \<^emph> (\<upharpoonleft>b)"
    apply (rule upred_sep_comm) by (rule upred_sep_comm2_eq)

lemma move_disj: "P\<^emph>(Q\<or>\<^sub>uR) = (Q\<or>\<^sub>uR) \<^emph> P" by (rule upred_sep_comm)
    
lemmas new_lock_simps[simp] = subst'_def iris_simp emp_rule pull_exists_eq pull_exists_eq' move_pure
  move_disj

lemma newlock_spec:
  "{{ upred_emp }} App newlock #[()] {{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}"
  apply (step | simp)+
  apply (rule add_holds[OF lock_alloc])
  apply (step | simp)+
  subgoal for l R \<gamma>
  apply (rule add_holds[OF inv_alloc[of "lock_inv _ _ R"]])
  by (step | simp)+
  done
end
end