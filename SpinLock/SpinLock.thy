theory SpinLock
imports "../SpanningTree/Spanning" BruteForceAutomation
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

lemma is_lock_pers: "persistent (is_lock \<gamma> lk R)" 
  unfolding is_lock_def by (log_prog_solver)
declare is_lock_pers[unfolded is_lock_def, pers_rule, log_prog_rule]
  
lemma locked_timeless: "timeless (locked \<gamma>)"
  by (auto simp: constr_lock_def locked_def intro!: own_timeless' log_prog_rule)
declare locked_timeless[unfolded locked_def, timeless_rule, log_prog_rule]
  
lemma lock_alloc: "\<exists>\<^sub>u \<gamma>.\<Rrightarrow>\<^sub>b (locked \<gamma>)"
  apply iIntro
  apply (iExistsR "0::nat")
  unfolding locked_def
  apply (entails_substR rule: rule: own_alloc)
  by (auto simp: valid_def constr_lock_def prod_n_valid_def \<epsilon>_n_valid valid_raw_ex_def)

lemmas [iris_simp] = lock_inv_def locked_def is_lock_def newlock_def acquire_def release_def
  
lemma newlock_spec:
  "{{ upred_emp }} App newlock #[()] {{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}"
  \<comment> \<open>Unfold newlock definition\<close>
  apply (auto simp: newlock_def subst'_def intro!: wp_pure[OF pure_exec_beta])
  \<comment> \<open>Remove wp based on @{thm wp_alloc}.\<close>
  apply (iApply rule: wp_alloc)
  apply (iDestruct rule: wp_mono)
  \<comment> \<open>Allocate lock and \<^const>\<open>lock_inv\<close>.\<close>
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
  by (iExistsR \<gamma>)
  oops

(* Once again with another wp rule. Is more similar to the Coq version.*)
lemma newlock_spec:
  "{{ upred_emp }} App newlock #[()] {{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}"
  apply (auto simp: newlock_def subst'_def intro!: wp_pure[OF pure_exec_beta])
  apply (iWP rule: wp_alloc')
  apply (entails_substR rule: wp_value)
  apply iForallR
  apply (rule upred_wandI)
  apply (iDestruct rule: lock_alloc)
  apply (iMod rule: upd_fupd)
  subgoal for l R \<gamma>
  apply (iMod_step "?P" rule: inv_alloc[of "lock_inv _ _ R" _ lockN])
  apply (entails_substR rule: upred_laterI)
  apply iExistsR2
  apply (iFrame2 "?l\<mapsto>\<^sub>u?b") by frame_single+
  oops

lemma release_spec: 
  "{{ is_lock \<gamma> lk R \<^emph> locked \<gamma> \<^emph> R }} App release lk {{ \<lambda>_. upred_emp }}"  
  \<comment> \<open>Unfold release definition\<close>
  apply (simp add: release_def is_lock_def upred_pure_sep_conj' pull_exists_eq pull_exists_eq')
  apply (iDestruct rule: wp_pure[OF pure_exec_beta]) subgoal for l
  \<comment> \<open>Open invaraint\<close>
  apply (iMod rule: inv_acc[to_entailment,OF subset_UNIV])
  \<comment> \<open>Apply @{thm wp_store}\<close>
  apply (move_sepL "\<triangleright> ?P")
  unfolding upred_later_exists
  apply iExistsL
  apply (iApply rule: upred_entail_eqL[OF upred_later_sep])
  apply (move_sepL "\<triangleright>(?l\<mapsto>\<^sub>u?v)")
  apply (rule elim_modal_entails'[OF elim_modal_timeless']) apply log_prog_solver+
  apply (iWP rule: wp_store'[simplified])
  \<comment> \<open>Cleanup\<close>
  apply (entails_substR rule: upred_laterI)
  apply (entails_substR rule: wp_value)
  apply (iApply_wand_as_rule "\<exists>\<^sub>u (x::bool). ?P x" "(?l\<mapsto>\<^sub>u?v)\<^emph>Own ?x\<^emph>R")
  apply (iExistsR False)
  apply (iApply rule: upred_laterI)
  apply (rule upred_later_mono_extR)
  by frame_single+
  oops 
  
lemmas spinlock_intros[intro] = wp_store'[simplified] 
  upred_entails_substE[OF upred_entail_eqL[OF upred_later_sep]]
  wp_pure[OF pure_exec_beta] wp_alloc' upred_entails_trans[OF _ wp_value]
  wp_mono upred_forallI upred_wandI upred_existsE'
  upred_entails_substE[OF upd_fupd[to_entailment]] elim_modal_entails'[OF elim_modal_fupd]
  elim_modal_entails[OF elim_modal_timeless'] elim_modal_entails'[OF elim_modal_timeless']
  upred_entails_trans[OF upred_wand_apply'] upred_entails_trans[OF _ upred_laterI] log_prog_rule
  upred_existsI upred_pure_impl upred_pure_impl' upred_pureI upred_pureI' upred_entails_refl 
  upred_weakeningR upred_weakeningL fupd_mono upred_entails_conjI  
  framing' can_be_split_refl can_be_split_baseR can_be_split_sepL
  elim_modal_entails'[OF elim_modal_fupd_wp_atomic]
    
lemma move_pure: "(\<upharpoonleft>b) \<^emph> P = P \<^emph> \<upharpoonleft>b" "P \<^emph> (\<upharpoonleft>b) \<^emph> Q = P \<^emph> Q \<^emph> (\<upharpoonleft>b)"
    apply (rule upred_sep_comm) by (rule upred_sep_comm2_eq)

lemma move_disj: "P\<^emph>(Q\<or>\<^sub>uR) = (Q\<or>\<^sub>uR) \<^emph> P" by (rule upred_sep_comm)

lemmas new_lock_simps[simp] = iris_simp pull_exists_eq pull_exists_eq' move_pure
  move_disj upred_later_exists

definition diaframe_hint :: "iprop \<Rightarrow> ('b \<Rightarrow> iprop) \<Rightarrow> (iprop \<Rightarrow> iprop) \<Rightarrow> ('a \<Rightarrow> iprop) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> iprop) \<Rightarrow> bool" where
  "diaframe_hint H L M A U \<equiv> \<forall>y::'b. (H \<^emph> L y \<turnstile> M (\<exists>\<^sub>u x::'a. A x \<^emph> U y x))"

lemma hintE: "diaframe_hint H L M A U \<Longrightarrow> (\<And>y::'b. (H \<^emph> L y \<turnstile> M (\<exists>\<^sub>u x::'a. A x \<^emph> U y x)))"
  unfolding diaframe_hint_def by simp
  
lemma inv_hint: "diaframe_hint upred_emp (\<lambda>x::'a. \<triangleright>(L x)) (linear_fupd E) (\<lambda>x::'a. inv N (L x)) (\<lambda>_ x::'a. inv N (L x))"
  apply (auto simp: diaframe_hint_def)
  apply (iMod rule: inv_alloc[to_entailment])
  apply iExistsR2
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF persistent_dupl]])
  by auto

lemma biabd_hint_apply_aux: 
  assumes "diaframe_hint H L (fancy_upd E3 E2) A U"
  shows "H \<^emph> \<Turnstile>{E1,E3}=> (\<exists>\<^sub>u y. L y \<^emph> (\<forall>\<^sub>u x. (U y x) -\<^emph> (G x))) \<turnstile> \<Turnstile>{E1,E2}=> (\<exists>\<^sub>u x. G x \<^emph> A x)"
  apply (entails_substR rule: fupd_mask_trans[of _ E3])
  apply (iMod rule: fupd_frame_r[where ?R=H])
  apply iExistsL
  apply (iApply rule: hintE[OF assms])
  apply (iMod rule: fupd_frame_r[where ?R="(\<forall>\<^sub>ux. U _ x -\<^emph> G x)"])
  apply iExistsL subgoal for y x
  apply (iExistsR x)
  apply (rule pull_forall_antecedent')
  apply (rule upred_entails_trans[OF upred_forall_inst[of _ x]])
  by auto
  done
  
lemma biabd_hint_apply: 
assumes "diaframe_hint H L (fancy_upd E3 E2) A U" "\<Delta> \<turnstile> \<Turnstile>{E1,E3}=> (\<exists>\<^sub>u y. L y \<^emph> (\<forall>\<^sub>u x. (U y x) -\<^emph> (G x)))"
shows "\<Delta> \<^emph> H \<turnstile> \<Turnstile>{E1,E2}=> (\<exists>\<^sub>u x. G x \<^emph> A x)"
proof -
  from biabd_hint_apply_aux[OF assms(1)] 
  have aux: "(\<Turnstile>{E1,E3}=>(\<exists>\<^sub>u y. L y \<^emph> (\<forall>\<^sub>u x. (U y x) -\<^emph> (G x)))) \<^emph> H \<turnstile> (\<Turnstile>{E1,E2}=>(\<exists>\<^sub>ux. G x \<^emph> A x))"
    apply (subst (2) upred_sep_comm) by simp
  show ?thesis
    apply (rule upred_entails_trans[OF upred_sep_mono[OF assms(2) upred_entails_refl[of H]]])
    by (rule aux)
qed

lemma biabd_hint_apply': 
assumes "diaframe_hint H L (fancy_upd E3 E2) (\<lambda>_. A) (\<lambda>y _. U y)" "\<Delta> \<turnstile> \<Turnstile>{E1,E3}=> (\<exists>\<^sub>u y. L y \<^emph> ((U y) -\<^emph> G))"
shows "\<Delta> \<^emph> H \<turnstile> \<Turnstile>{E1,E2}=> (G \<^emph> A)"
proof -
  from assms(2) have "\<Delta> \<turnstile> \<Turnstile>{E1,E3}=> (\<exists>\<^sub>u y. L y \<^emph> (\<forall>\<^sub>u x. ((\<lambda>y _. U y) y x) -\<^emph> G))" 
    by (simp add: drop_forall)
  from biabd_hint_apply[OF assms(1) this, unfolded drop_exists] show ?thesis .
qed
  
lemma wp_store_hint:"diaframe_hint upred_emp (\<lambda>_. \<Turnstile>{UNIV,E}=>(\<exists>\<^sub>u v'. (\<triangleright>(l\<mapsto>\<^sub>uv')) \<^emph> (\<triangleright>(((l\<mapsto>\<^sub>uv) ={E,UNIV}=\<^emph> \<Phi> #[()])))))
  (linear_fupd UNIV) (\<lambda>_. WP (Store #[l] (Val v)) {{ \<Phi> }}) (\<lambda>_ _. upred_emp)"
  unfolding diaframe_hint_def
  apply (simp add: drop_exists)
  apply(entails_substR rule: fupd_intro)
  apply (rule elim_modal_entails[OF elim_modal_fupd_wp_atomic[OF atomic_store]])
  apply iExistsL
  apply (move_sepL "\<triangleright>(?l\<mapsto>\<^sub>u?v)")
  apply later_elim
  apply (rule wp_store'[unfolded to_val_simp])
  apply (rule upred_later_mono_extL)
  apply (rule upred_entails_trans[OF _ wp_value])
  by iApply_wand
  
lemmas inv_alloc' = biabd_hint_apply[OF inv_hint]
lemmas store_hint = biabd_hint_apply'[OF wp_store_hint]

lemma combine_exist:"(\<exists>\<^sub>u x. (\<exists>\<^sub>u y. P x y)) = (\<exists>\<^sub>u xy. P ((\<lambda>(x,y). x) xy) ((\<lambda>(x,y). y) xy))"
  apply transfer' by simp

lemma newlock_spec:
  "{{ upred_emp }} App newlock #[()] {{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}"
  apply (simp | step)+
  apply (rule add_holds[OF lock_alloc])
  apply (simp | step)+
  apply (rule inv_alloc'[where ?G = "\<lambda> _. upred_emp",simplified])
  apply (entails_substR rule: fupd_intro[to_entailment])
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  oops

ML \<open>
  val x = (HOLogic.case_prod_const (dummyT,dummyT,dummyT))$ Abs ("\<gamma>", dummyT, Abs ("y", dummyT, Bound 0))$
    Var (("x",0), HOLogic.mk_prodT (dummyT,dummyT))
  val y = Free ("y", \<^typ>\<open>nat\<close>)
  val init = Envir.empty 0
  val z = Unify.unifiers (Context.Proof \<^context>, init, [(y,x)])
  val a = Seq.pull z
  val b = Unify.matchers (Context.Proof \<^context>) [(y,x)] |> Seq.pull
  val _ = Syntax.pretty_term \<^context> x |> Pretty.writeln
  val e = Thm.beta_conversion true (Thm.cterm_of \<^context> x)
  val f = Term.could_beta_contract x
\<close>

lemma move_invR: "inv N Q \<^emph> P = P \<^emph> inv N Q" "P \<^emph> inv N R \<^emph> Q = P \<^emph> Q \<^emph> inv N R"
  apply (rule upred_sep_comm) by (rule upred_sep_comm2_eq)

lemma move_invL: "P \<^emph> inv N Q = inv N Q \<^emph> P" by (rule upred_sep_comm)

lemma move_closerL: "P \<^emph> (Q={UNIV - names N,UNIV}=\<^emph>upred_emp) = (Q={UNIV - names N,UNIV}=\<^emph>upred_emp) \<^emph> P"
  by (rule upred_sep_comm)

lemma move_closerR: "(Q={UNIV - names N,UNIV}=\<^emph>upred_emp) \<^emph> P = P \<^emph> (Q={UNIV - names N,UNIV}=\<^emph>upred_emp)" 
  "P \<^emph> (R={UNIV - names N,UNIV}=\<^emph>upred_emp) \<^emph> Q = P \<^emph> Q \<^emph> (R={UNIV - names N,UNIV}=\<^emph>upred_emp)"
  apply (rule upred_sep_comm) by (rule upred_sep_comm2_eq)
  
method inv_opener = 
  ((unfold move_invR upred_pure_sep_conj')+)?,
  (rule upred_entails_substE[OF upred_entail_eqR[OF persistent_dupl]]
  | rule upred_entails_substE'[OF upred_entail_eqR[OF persistent_dupl]]),
  fast, unfold upred_sep_assoc_eq,
  (rule upred_entails_substE[OF inv_acc[to_entailment,OF subset_UNIV]]
  | rule upred_entails_substE'[OF inv_acc[to_entailment,OF subset_UNIV]]),
  (unfold move_closerL)?

lemma release_spec: 
  "{{ is_lock \<gamma> lk R \<^emph> locked \<gamma> \<^emph> R }} App release lk {{ \<lambda>_. upred_emp }}" 
  apply (simp | step)+
  apply inv_opener
  apply (simp | step)+
  unfolding move_closerR
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  apply (simp | step)
  subgoal apply (rule split_last_frame) by step+
  apply (simp | step)
  oops

declare spinlock_intros[rule del]
declare new_lock_simps[simp del]

declare frame_rule_apply[OF upred_entails_trans[OF upred_entails_trans[OF lock_alloc[to_entailment] upred_exist_mono[OF upd_fupd[to_entailment]], unfolded locked_def] fupd_exists_lift], alloc_rule]
declare upred_later_exists[iris_simp]
declare upred_entails_trans[OF store_hint[where ?G = upred_emp, unfolded emp_rule to_val_simp] fupd_wp, wp_symbolic_execution_steps]
declare frame_baseL[frame_rule]

lemma newlock_spec:
  "{{{ upred_emp }}} App newlock #[()] {{{ \<lambda>lk. \<forall>\<^sub>u R. (R ={UNIV}=\<^emph> (\<exists>\<^sub>u \<gamma>. is_lock \<gamma> lk R)) }}}"
  by brute_force_solver

lemma release_spec: 
  "{{{ is_lock \<gamma> lk R \<^emph> locked \<gamma> \<^emph> R }}} App release lk {{{ \<lambda>_. upred_emp }}}"
  by brute_force_solver
end