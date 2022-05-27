theory Invariant
imports ViewShift Automation
begin

subsubsection \<open>Impredicative Invariants\<close>

context 
fixes get_inv :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> inv option"
  and put_inv
assumes inv_inG: "inG get_inv put_inv"
begin

abbreviation fancy_upd' ("\<Turnstile>{_,_}=>_") where "fancy_upd' \<equiv> fancy_upd put_inv"
abbreviation wand_fupd' ("_={_,_}=\<^emph>_") where "wand_fupd' \<equiv> wand_fupd put_inv"
abbreviation linear_fupd' ("\<Turnstile>{_}=>_") where "linear_fupd' \<equiv> linear_fupd put_inv"
abbreviation wand_linear_fupd' ("_={_}=\<^emph>_") where "wand_linear_fupd' \<equiv> wand_linear_fupd put_inv"
abbreviation inv_raw where "inv_raw \<equiv> WorldSatisfaction.inv_raw put_inv"
abbreviation wsat :: "'res upred_f" where "wsat \<equiv> WorldSatisfaction.wsat put_inv"
abbreviation ownE :: "mask \<Rightarrow> 'res upred_f" where "ownE \<equiv> WorldSatisfaction.ownE put_inv"
abbreviation ownD :: "name fset \<Rightarrow> 'res upred_f" where "ownD \<equiv> WorldSatisfaction.ownD put_inv"
abbreviation ownI :: "name \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" where "ownI \<equiv> WorldSatisfaction.ownI put_inv"

text \<open>Semantic invariant definition\<close>
definition inv :: "namespace \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" where
  "inv N P = \<box>(\<forall>\<^sub>u E. ((\<upharpoonleft>((names N) \<subseteq> E)) \<longrightarrow>\<^sub>u 
    (\<Turnstile>{E,E-(names N)}=> ((\<triangleright>P) \<^emph> ((\<triangleright>P) ={E-(names N), E}=\<^emph> \<upharpoonleft>True)))))"

lemma superset_split: "s \<subseteq> t \<Longrightarrow> t = s \<union> (t-s)" by auto
    
lemma inv_raw_acc: "names N \<subseteq> E \<Longrightarrow> 
  ((inv_raw N P) ={E, E-(names N)}=\<^emph> ((\<triangleright>P) \<^emph> ((\<triangleright>P) ={E-(names N), E}=\<^emph> \<upharpoonleft>True)))"
apply (auto simp: fancy_upd_def[OF inv_inG] upred_sep_assoc_eq inv_raw_def[OF inv_inG] intro!: upred_wand_holdsI upred_existsE')
apply (rule upred_entails_trans[OF upred_entail_eqR[OF persistent_holds_sep']], pers_solver, rule inv_inG)
apply (auto intro!: upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]] upred_pure_impl)
apply (auto simp: upred_sep_assoc_eq intro!: upred_wandI)
apply (subst superset_split[of "names N"], assumption)
apply (rule upred_entails_substE[OF upred_entail_eqL[OF ownE_op_minus[OF inv_inG]]])
apply (auto simp: upred_sep_assoc_eq)
subgoal for i
apply (simp add: dnames_def)
apply (subst superset_split[of "{i}" "names N"], simp)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_entail_eqL[OF ownE_op_minus[OF inv_inG]], of "{i}" "names N"])
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_trans[OF _ updI] upred_entails_trans[OF _ except_zeroI])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm4_1])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_entail_eqR[OF persistent_dupl]])
apply (pers_solver, rule inv_inG)
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm3L])
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF ownI_open[OF inv_inG], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_frame)
apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3L])
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_frame)
apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: upred_sep_assoc_eq intro!: upred_frame upred_wandI)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_substE[OF ownI_close[OF inv_inG], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: insert_absorb intro!: upred_entails_substE[OF 
    upred_entail_eqR[OF ownE_op_minus[OF inv_inG]], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: Un_absorb1 intro!: upred_entails_substE[OF upred_entail_eqR[OF 
    ownE_op_minus[OF inv_inG]], unfolded upred_sep_assoc_eq] upred_entails_trans[OF _ updI]
    upred_entails_trans[OF _ except_zeroI])
apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
by (auto simp: upred_true_sep intro!: upred_frame)
done

lemma fresh_inv_name: "\<exists>\<iota>. \<iota> |\<notin>| E \<and> \<iota> \<in> names N"
proof -
  from infinite_names have "names N - fset E \<noteq> {}"
     using finite_fset infinite_super by fastforce    
  then obtain \<iota> where "\<iota> \<in> names N - fset E" unfolding dnames_def by (cases E) auto
  then have "\<iota> |\<notin>| E \<and> \<iota> \<in> names N" by (auto simp add: dnames_def fmember.rep_eq)
  then show ?thesis by blast
qed

lemma inv_raw_alloc: "(\<triangleright>P) ={E}=\<^emph> (inv_raw N P)"
apply (auto simp: fancy_upd_def[OF inv_inG] upred_sep_assoc_eq intro!: upred_wand_holdsI upred_wandI)
apply (subst upred_sep_comm2_eq[of wsat])
apply (rule upred_entails_trans[OF _ upd_mono,OF _ except_zero_sepR])
apply (auto intro!: upred_entails_trans[OF _ upd_frameL] upred_frame)
apply (rule upred_wand_holdsE)
apply (subst upred_sep_comm)
apply (rule upred_entails_wand_holdsR[OF _ ownI_alloc[OF inv_inG, of "\<lambda>i. i \<in> names N"], 
    OF _ allI[OF fresh_inv_name, of id, simplified]])
apply (rule upd_mono)
apply (auto intro!: upred_existsE')
apply (subst upred_sep_comm[of wsat])
apply (subst upred_sep_comm2_eq)
apply (auto intro!: upred_entails_trans[OF _ except_zeroI] upred_frame)
unfolding inv_raw_def[OF inv_inG]
subgoal for i
apply (rule upred_existsI[of _ _ i])
apply (subst upred_sep_comm)
by (auto simp: dnames_def intro!:upred_pure_impl upred_entails_conjI upred_pureI)
done

lemma inv_raw_alloc_open: "names N \<subseteq> E \<Longrightarrow>
  \<Turnstile>{E, E-names N}=> (inv_raw N P \<^emph> ((\<triangleright>P) ={E-names N, E}=\<^emph> upred_emp))"
  unfolding fancy_upd_def[OF inv_inG]
apply (rule upred_wand_holdsI)
apply (rule upred_wandE)
apply (rule upred_entails_trans[OF upred_wand_holdsE[OF ownI_alloc_open[OF inv_inG, of "\<lambda>i. i \<in> names N"]],
  OF allI[OF fresh_inv_name, of id, simplified], of P])
apply (auto simp: pull_exists_eq intro!: upred_wandI upred_entails_trans[OF upd_frameL] upd_mono upred_existsE')
apply (rule upred_entails_trans[OF upred_sep_comm4_1])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_pure_impl)
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
subgoal for i
apply (rule split_trans[of _ "ownE E \<^emph> ownI i P" "(ownE {i} -\<^emph> wsat) \<^emph> ownD {|i|} \<^emph> ownI i P" 
  "ownE {i} \<^emph> ownE (names N - {i}) \<^emph> ownE (E - names N)", unfolded upred_sep_assoc_eq])
apply(rule can_be_split_R_R[OF persistent_dupl_split[OF persistent_ownI[OF inv_inG]], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm2L]])
apply (auto simp: insert_absorb intro!: upred_entails_substI[OF 
    upred_entail_eqL[OF ownE_op_minus[OF inv_inG]], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm]])
apply (auto simp: Un_absorb1 upred_weakeningL upred_sep_assoc_eq
  intro!: upred_entails_trans[OF _ upred_entail_eqL[OF ownE_op_minus[OF inv_inG]], unfolded upred_sep_assoc_eq] 
  upred_entails_trans[OF _ except_zeroI])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF _ upred_sep_comm3M])
apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
apply (rule upred_frame)
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm4_1])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule split_frame[of _ "ownE {i} \<^emph> (ownE {i} -\<^emph> wsat) \<^emph> ownI i P" 
  "ownE (names N - {i}) \<^emph> ownD {|i|}\<^emph> ownI i P" _ wsat
  "inv_raw N P \<^emph> ((\<triangleright>P) -\<^emph> (wsat \<^emph> ownE (E - names N)) ==\<^emph> \<diamondop>(wsat \<^emph> ownE E \<^emph> upred_emp))", 
  unfolded upred_sep_assoc_eq])
apply (rule can_be_split_mono[OF _ persistent_dupl_split[OF persistent_ownI[OF inv_inG]], unfolded upred_sep_assoc_eq])
apply (rule can_be_split_rev)
apply (rule can_be_split_refl)
subgoal unfolding can_be_split_def by (simp add: upred_entails_eq_eq upred_sep_assoc_eq)
apply (auto intro: upred_entails_trans[OF upred_weakeningL] upred_wand_apply)
apply (rule split_frame[of _ "ownI i P" _ _ "inv_raw N P"])
apply (rule can_be_split_rev)
apply (rule persistent_dupl_split, pers_solver, rule inv_inG)
apply (rule can_be_split_refl)
apply (auto simp: inv_raw_def[OF inv_inG] dnames_def upred_true_conj' upred_sep_assoc_eq intro!: upred_existsI[of _ _ i] upred_wandI)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]]; simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_substE[OF ownI_close[OF inv_inG], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: insert_absorb intro!: upred_entails_substE[OF 
    upred_entail_eqR[OF ownE_op_minus[OF inv_inG]], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
by (auto simp: Un_absorb1 upred_true_sep intro!: upred_entails_substE[OF 
    upred_entail_eqR[OF ownE_op_minus[OF inv_inG]], unfolded upred_sep_assoc_eq] upred_entails_trans[OF _ updI]
    upred_entails_trans[OF _ except_zeroI])
done

lemma inv_raw_to_inv: "inv_raw N P -\<^emph> inv N P"
unfolding inv_def
apply (auto intro!: upred_wand_holdsI upred_entails_trans[OF _ upred_entail_eqL[OF pers_forall]] 
  upred_forallI upred_entails_trans[OF _ upred_entail_eqR[OF upred_pers_impl_pure]] upred_implI_pure)
subgoal for E
apply (rule add_holds[OF upred_holds_persis[OF inv_raw_acc[of N E P]]], assumption)
by (auto intro!: upred_persis_frame[OF _ upred_wand_apply], pers_solver, rule inv_inG)
done

text \<open>
  The follow lemmata are the public API for invariants and should be enough to handle most proofs
  with invariants.
\<close>

lemma persistent_inv [pers_rule,log_prog_rule]: "persistent (inv N P)"
  unfolding inv_def by pers_solver

lemma inv_alter: "inv N P -\<^emph> (\<triangleright>\<box>(P -\<^emph> (Q \<^emph> (Q-\<^emph>P)))) -\<^emph> inv N Q"
apply (auto simp: inv_def intro!: upred_wand_holds2I upred_entails_trans[OF _ upred_entail_eqL[OF 
    pers_forall]] upred_forallI upred_entails_trans[OF _ upred_entail_eqR[OF upred_pers_impl_pure]]
    upred_implI_pure)
apply (rule persistent_persisI, pers_solver)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
subgoal for E
apply (auto intro!: upred_entails_substE[OF upred_persis_mono[OF upred_forall_inst[of _ E]]] 
  upred_entails_substE[OF upred_persis_mono[OF upred_entail_eqL[OF upred_emp_impl]]])
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_substE[OF upred_persisE] fupd_frame_mono[OF inv_inG])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule split_trans[OF _ upred_entails_trans[OF upred_entail_eqR[OF upred_later_sep] upred_later_mono[OF
  upred_persis_mono_frame[OF upred_wand_apply[of P "Q\<^emph>(Q-\<^emph>P)"]]]]])
apply (rule can_be_split_sepL)
apply (rule can_be_split_rev)
apply (rule can_be_split_refl)
apply (auto intro!: split_frame[OF _ can_be_split_refl, of _ "\<triangleright>Q"])
apply (rule can_be_split_sepR)
unfolding can_be_split_def
apply (rule upred_later_sep)
apply (rule upred_wandI)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_later_sep], OF upred_entails_substE[OF
    upred_later_mono[OF upred_wand_apply]], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
by (auto intro: upred_entails_trans[OF upred_wand_apply])
done

lemma inv_iff: "inv N P -\<^emph> (\<triangleright>\<box>((P \<longrightarrow>\<^sub>u Q) \<and>\<^sub>u (Q\<longrightarrow>\<^sub>uP))) -\<^emph> inv N Q"
apply (auto intro!: upred_wand_holds2I upred_entails_trans[OF _ upred_wand_holds2E[OF inv_alter], of _ N P])
apply (auto intro!: upred_sep_mono upred_later_mono)
apply (rule upred_entails_trans[OF upred_entail_eqR[OF persistent_dupl]], pers_solver)
apply (rule upred_persis_frame, pers_solver)
apply (auto intro!: upred_wandI)
apply (rule split_frame[of _ "((P \<longrightarrow>\<^sub>u Q) \<and>\<^sub>u (Q \<longrightarrow>\<^sub>u P)) \<^emph> P" _ _ Q])
apply (rule can_be_split_sepL; rule can_be_split_rev; rule can_be_split_refl)
apply (rule can_be_split_refl)
apply (rule upred_entails_trans[OF upred_entails_conj_sep])
apply (subst upred_conj_comm)
apply (subst upred_conj_comm2R)
apply (auto simp: upred_weakeningR' intro: upred_entails_substE'[OF upred_impl_apply, unfolded upred_conj_assoc])
apply (rule upred_entails_trans[OF upred_persisE])
apply (rule upred_wandI)
apply (rule upred_entails_trans[OF upred_entails_conj_sep])
apply (subst upred_conj_comm2R)
by (auto simp: upred_weakeningR' intro: upred_entails_substE'[OF upred_impl_apply, unfolded upred_conj_assoc])

lemma inv_alloc: "(\<triangleright>P) ={E}=\<^emph> inv N P"
  by (auto intro!: upred_wand_holdsI upred_entails_trans[OF _ fupd_mono[OF inv_inG upred_wand_holdsE[OF 
    inv_raw_to_inv]]] upred_wand_holdsE[OF inv_raw_alloc])

lemma inv_alloc_open: "names N \<subseteq> E \<Longrightarrow>
  \<Turnstile>{E, E-names N}=> (inv N P \<^emph> ((\<triangleright>P) ={E-names N, E}=\<^emph> upred_emp))"
apply (auto simp: upred_holds_entails)
apply (rule add_holds[OF inv_raw_alloc_open[of N E P]], simp)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF upred_weakeningL])
by (auto simp: upred_wand_holdsE[OF inv_raw_to_inv] intro!: fupd_mono[OF inv_inG] upred_sep_mono)

lemma inv_acc: "names N \<subseteq> E \<Longrightarrow> 
  ((inv N P) ={E, E-(names N)}=\<^emph> ((\<triangleright>P) \<^emph> ((\<triangleright>P) ={E-(names N), E}=\<^emph> \<upharpoonleft>True)))"
  by (auto simp: inv_def intro!: upred_wand_holdsI upred_entails_trans[OF upred_persisE]
    upred_entails_trans[OF upred_forall_inst[of _ E]] upred_entails_trans[OF upred_entail_eqL[OF upred_emp_impl]])

lemma inv_combine: "\<lbrakk>names N1 \<inter> names N2 = {}; names N1 \<union> names N2 \<subseteq> names N\<rbrakk> \<Longrightarrow>
    inv N1 P -\<^emph> inv N2 Q -\<^emph> inv N (P\<^emph>Q)"
unfolding inv_def
apply (auto intro!: upred_wand_holds2I upred_persis_frame upred_forallI upred_implI_pure, pers_solver)
subgoal for E
apply (auto intro!: upred_entails_substE[OF upred_forall_inst[of _ "E - names N1"]])
apply (auto intro!: upred_entails_substE[OF upred_implE_pure, OF  _ upred_entails_refl])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (auto intro!: upred_entails_substE[OF upred_persisE] upred_entails_substE[OF upred_forall_inst[of _ E]])
apply (auto intro!: upred_entails_substE[OF upred_implE_pure, OF _ upred_entails_refl])
apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of _ "E-names N1"]])
apply (rule fupd_frame_mono[OF inv_inG])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of _ "E-names N1-names N2"]])
apply (auto simp: upred_sep_assoc_eq intro!: fupd_frame_mono[OF inv_inG] upred_entails_trans[OF _ 
  upred_wand_holdsE[OF fupd_frame_split[OF inv_inG, of _ "(\<triangleright>(P \<^emph> Q))={E - names N,E}=\<^emph>upred_emp" "\<triangleright>(P\<^emph>Q)", 
  OF can_be_split_rev, OF can_be_split_refl]]] upred_entails_substI[OF upred_entail_eqR[OF upred_later_sep]])
apply (rule upred_entails_trans[OF upred_sep_comm2R], rule upred_frame)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R], rule upred_frame)
apply (auto intro!: upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_mask_intro[OF inv_inG]]])
apply (auto simp: upred_sep_assoc_eq intro!: upred_wandI upred_entails_substE[OF upred_entail_eqL[OF 
    upred_later_sep]])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of _ "E-names N1-names N2"]])
apply (auto simp: upred_true_sep intro!: fupd_frame_mono[OF inv_inG])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of _ "E-names N1"]])
apply (auto simp: upred_true_sep intro!: fupd_frame_mono[OF inv_inG])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
by (auto intro: upred_entails_trans[OF upred_wand_apply])
done

lemma inv_combine_dup_l: "(\<box>(P -\<^emph> (P\<^emph>P))) -\<^emph> inv N P -\<^emph> inv N Q -\<^emph> inv N (P \<^emph>Q)"
apply (auto simp: inv_def intro!: upred_wand_holds2I upred_wandI upred_persis_frame upred_forallI 
  upred_implI_pure, pers_solver)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
subgoal for E
apply (auto intro!: upred_entails_substE[OF upred_persisE] upred_entails_substE[OF upred_forall_inst[of _ E]]
  upred_entails_substE[OF upred_entail_eqL[OF upred_emp_impl]])
apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of _ "E-names N"]])
apply (auto simp: upred_sep_assoc_eq intro!: fupd_frame_mono[OF inv_inG])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3L])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_substE[OF upred_persisE] upred_entails_substE[OF 
  upred_later_mono_extL[OF upred_wand_apply], unfolded upred_sep_assoc_eq]
  upred_entails_substE[OF upred_entail_eqL[OF upred_later_sep]])
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_trans[OF _ upred_wand_holdsE[OF 
  fupd_frame_split[OF inv_inG, of _ "(\<triangleright>Q)\<^emph>((\<triangleright>(P \<^emph> Q))={E - names N,E}=\<^emph>upred_emp)" "\<triangleright>P"], OF can_be_split_sepL,
  OF can_be_split_rev, OF can_be_splitI[OF upred_later_sep]]])
apply (rule upred_frame)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of _ E]])
apply (auto simp: upred_true_sep intro!: fupd_frame_mono[OF inv_inG])
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_trans[OF upred_forall_inst[of _ E]] 
  upred_entails_trans[OF upred_entail_eqL[OF upred_emp_impl]] fupd_mono[OF inv_inG] upred_sep_mono upred_wandI 
  upred_entails_substE[OF upred_entail_eqL[OF upred_later_sep]])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
by (rule upred_weakeningR)
done
end

subsubsection \<open>Cancelable Invariants\<close>
type_synonym cinvG = frac

context 
fixes get_cinv :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> cinvG option option"
  and put_cinv
  and get_inv :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> inv option"
  and put_inv
assumes cinv_inG: "inG get_cinv put_cinv"
  and inv_inG: "inG get_inv put_inv"
begin

abbreviation fancy_upd'' ("\<Turnstile>{_,_}=>_") where "fancy_upd'' \<equiv> fancy_upd put_inv"
abbreviation wand_fupd'' ("_={_,_}=\<^emph>_") where "wand_fupd'' \<equiv> wand_fupd put_inv"
abbreviation linear_fupd'' ("\<Turnstile>{_}=>_") where "linear_fupd'' \<equiv> linear_fupd put_inv"
abbreviation wand_linear_fupd'' ("_={_}=\<^emph>_") where "wand_linear_fupd'' \<equiv> wand_linear_fupd put_inv"
  
definition cinv_own :: "gname \<Rightarrow> frac \<Rightarrow> 'res upred_f" where "cinv_own \<gamma> p = own put_cinv \<gamma> (Some p)"
definition cinv :: "namespace \<Rightarrow> gname \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" where 
  "cinv N \<gamma> P = inv put_inv N (P \<or>\<^sub>u cinv_own \<gamma> 1)"

lemma cinv_persistent [pers_rule,log_prog_rule]: "persistent (cinv N \<gamma> P)"
  unfolding cinv_def by (rule persistent_inv[OF inv_inG])

lemma timeless_cinv_own: "timeless (cinv_own \<gamma> p)"
  unfolding cinv_own_def inG.own_def[OF cinv_inG]
  apply (rule own_timeless')
  unfolding dcamera_val_def discrete_val_def
  apply (auto simp: inG.put_ne[OF cinv_inG] ofe_refl ofe_limit valid_def inG.put_n_valid[OF cinv_inG]
    valid_raw_frac_def valid_raw_option_def)
  by (metis (mono_tags, lifting) cinv_inG d_equiv inG.put_ne inG.put_ne2)+

lemma cinv_upred_own_valid: "cinv_own \<gamma> q1 -\<^emph> cinv_own \<gamma> q2 -\<^emph> \<upharpoonleft>(q1\<cdot>q2\<le>1)"
unfolding cinv_own_def
apply (rule upred_entails_wand_holdsR2[OF _ inG.own_valid2[OF cinv_inG]])
apply (simp add: op_prod_def \<epsilon>_left_id op_option_def)
apply (simp add: upred_entails.rep_eq upred_valid.rep_eq upred_pure.rep_eq prod_n_valid_def \<epsilon>_n_valid)
apply (simp add: valid_raw_option_def valid_frac[symmetric] split: option.splits)
by (metis dcamera_valid_iff less_eq_frac.rep_eq one_frac.rep_eq valid_raw_frac.rep_eq)

lemma cinv_own_1_l: "cinv_own \<gamma> 1 -\<^emph> cinv_own \<gamma> q -\<^emph> \<upharpoonleft>False"
proof (rule upred_wand_holds2I)
  from one_op have "(1\<cdot>q \<le> 1) \<longleftrightarrow> False" by (simp add: less_le_not_le)
  with upred_wand_holds2E[OF cinv_upred_own_valid, of \<gamma> 1 q] show "cinv_own \<gamma> 1 \<^emph> cinv_own \<gamma> q \<turnstile> \<upharpoonleft>False" 
    by simp
qed

lemma cinv_acc_strong: "names N \<subseteq> E \<Longrightarrow>
  (cinv N \<gamma> P) -\<^emph> (cinv_own \<gamma> p ={E,E-names N}=\<^emph>
  ((\<triangleright>P) \<^emph> cinv_own \<gamma> p \<^emph> (\<forall>\<^sub>u E'. (((\<triangleright>P) \<or>\<^sub>u cinv_own \<gamma> 1) ={E',names N \<union> E'}=\<^emph> upred_emp))))"
  apply (rule upred_wand_holds2I)
  apply (rule add_holds[OF inv_acc[OF inv_inG, of N "names N", simplified]])
  apply (subst cinv_def)
  apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
  apply (rule upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
  apply (rule add_holds[OF fupd_mask_frameR[OF inv_inG, of "names N" "E-names N"]])
  apply simp
  apply (rule upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
  apply (simp add: Un_absorb1)
  apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of E "E -names N" "E-names N"]])
  apply (auto simp: upred_sep_assoc_eq intro!: fupd_frame_mono[OF inv_inG])
  apply (rule upred_entails_trans[OF upred_sep_comm2R])
  apply (rule upred_entails_substE[OF upred_entail_eqL[OF upred_later_disj]])
  apply (rule upred_disjE')
  apply (rule upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_frame_split[OF inv_inG]]]) prefer 2
  apply (rule can_be_split_rev) apply (rule can_be_split_sepR) apply (rule can_be_split_refl)
  apply (rule upred_frame)
  apply (rule upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_frame_split[OF inv_inG]]]) prefer 2
  apply (rule can_be_split_rev) apply (rule can_be_split_refl)
  apply (subst upred_sep_comm, rule upred_frame)
  apply (rule upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_intro[OF inv_inG]]])
  apply (auto intro!: upred_sep_mono upred_forallI)[1]
  subgoal for E'
    apply (rule upred_entails_trans[OF upred_wand_mono[OF upred_entail_eqR[OF upred_later_disj] upred_entails_refl]])
    apply (rule upred_wandI)
    apply (subst upred_sep_comm)
    apply (rule upred_entails_trans[OF upred_wand_apply'])
    apply (rule upred_disjE) apply (auto intro: upred_disjIL)
    apply (rule upred_entails_trans[OF upred_laterI]) apply (auto intro: upred_disjIR)
    apply (rule add_holds[OF fupd_mask_frameR[OF inv_inG, of "{}" E' "names N" upred_emp, simplified]])
    by (auto intro: upred_entails_trans[OF upred_wand_apply])
  apply (rule elim_modal_entails'[OF elim_modal_timeless[OF timeless_cinv_own[unfolded timeless_def] is_except_zero_fupd]])
  apply (rule inv_inG)  
  apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
  apply (rule upred_entails_trans[OF upred_sep_comm2R])
  by (auto intro: upred_entails_substE[OF upred_wand_holds2E[OF cinv_own_1_l], unfolded upred_sep_assoc_eq])

lemma cinv_acc: "names N \<subseteq> E \<Longrightarrow>
  ((cinv N \<gamma> P) -\<^emph> (cinv_own \<gamma> p ={E,E-names N}=\<^emph> ((\<triangleright>P) \<^emph> cinv_own \<gamma> p \<^emph> ((\<triangleright>P) ={E-names N,E}=\<^emph>upred_emp))))"
  apply (rule upred_wand_holdsI)
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF persistent_dupl]], pers_solver)
  apply (rule upred_wandI)
  apply (auto intro!: upred_entails_substE[OF upred_wand_holds2E[OF cinv_acc_strong], simplified upred_sep_assoc_eq, of N E])
  apply (rule upred_entails_trans[OF _ fupd_mask_trans[OF inv_inG, of E "E -names N" "E-names N"]])
  apply (auto simp: upred_sep_assoc_eq intro!: fupd_frame_mono[OF inv_inG])
  apply (rule upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_frame_split[OF inv_inG]]])
  prefer 2 apply (rule can_be_split_rev, rule can_be_split_refl, unfold upred_sep_assoc_eq)
  apply (rule upred_entails_trans[OF upred_sep_comm2R]) apply (rule upred_frame)  
  apply (rule upred_entails_trans[OF upred_sep_comm2R]) apply (rule upred_frame)
  apply (rule upred_entails_substE[OF upred_forall_inst[of _ "E-names N"]])
  apply (rule upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_intro[OF inv_inG]]])
  apply (rule upred_wandI)
  apply (rule upred_entails_trans[OF upred_sep_comm2R]) 
  apply (auto simp: Un_absorb1 intro!: upred_entails_substE[OF upred_wand_apply', unfolded upred_sep_assoc_eq] upred_disjIL) 
  by (rule upred_weakeningR)
end
end