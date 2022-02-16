theory Invariant
imports ViewShift
begin

subsubsection \<open>Impredicative Invariants\<close>

text \<open>Semantic invariant definition\<close>
definition inv :: "namespace \<Rightarrow> iprop \<Rightarrow> iprop" where
  "inv N P = \<box>(\<forall>\<^sub>u E. ((\<upharpoonleft>((dnames N) \<subseteq>\<^sub>d E)) \<longrightarrow>\<^sub>u 
    (\<Turnstile>{E,E-(dnames N)}=> ((\<triangleright>P) \<^emph> ((\<triangleright>P) ={E-(dnames N), E}=\<^emph> \<upharpoonleft>True)))))"

lemma inv_raw_acc: "dnames N \<subseteq>\<^sub>d E \<Longrightarrow> 
  ((inv_raw N P) ={E, E-(dnames N)}=\<^emph> ((\<triangleright>P) \<^emph> ((\<triangleright>P) ={E-(dnames N), E}=\<^emph> \<upharpoonleft>True)))"
apply (auto simp: fancy_upd_def upred_sep_assoc_eq inv_raw_def intro!: upred_wand_holdsI upred_existsE')
apply (rule upred_entails_trans[OF upred_entail_eqR[OF persistent_holds_sep']], pers_solver)
apply (auto intro!: upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]] upred_pure_impl)
apply (auto simp: upred_sep_assoc_eq intro!: upred_wandI)
apply (subst dsubs_op_minus[of "dnames N"], assumption)
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_substE[OF upred_entail_eqL[OF ownE_op_minus]])
subgoal for i
unfolding delem_dsubs[of i "dnames N"]
apply (subst dsubs_op_minus[of "DSet {i}" "dnames N"], assumption)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_substE[OF 
    upred_entail_eqL[OF ownE_op_minus], of "DSet {i}" "dnames N"] upred_entails_trans[OF _ updI]
    upred_entails_trans[OF _ except_zeroI])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm4_1])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_entail_eqR[OF persistent_dupl]])
apply pers_solver
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm3L])
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF ownI_open, unfolded upred_sep_assoc_eq])
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
apply (rule upred_entails_substE[OF ownI_close, unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: dsubs_op_minus[symmetric] intro!: upred_entails_substE[OF 
    upred_entail_eqR[OF ownE_op_minus], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: dsubs_op_minus[symmetric] intro!: upred_entails_substE[OF 
    upred_entail_eqR[OF ownE_op_minus], unfolded upred_sep_assoc_eq] upred_entails_trans[OF _ updI]
    upred_entails_trans[OF _ except_zeroI])
apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
by (auto simp: upred_true_sep intro!: upred_frame)
done

lemma fresh_inv_name: "\<exists>\<iota>. \<not> (\<iota> \<in>\<^sub>f E) \<and> \<iota> \<in>\<^sub>d dnames N"
proof -
  from infinite_names dset_of_finite_finite have "dnames N - dset_of_finite E \<noteq> DSet {}"
    unfolding dnames_def apply (cases E) apply auto using finite_fset infinite_super apply blast 
    using not_no_names by simp
  then obtain \<iota> where "\<iota> \<in>\<^sub>d dnames N - dset_of_finite E" unfolding dnames_def by (cases E) auto
  then have "\<not> (\<iota> \<in>\<^sub>f E) \<and> \<iota> \<in>\<^sub>d dnames N" apply (cases E) by (auto simp add: dnames_def fmember.rep_eq)
  then show ?thesis by blast
qed

lemma inv_raw_alloc: "(\<triangleright>P) ={E}=\<^emph> (inv_raw N P)"
apply (auto simp: fancy_upd_def upred_sep_assoc_eq intro!: upred_wand_holdsI upred_wandI)
apply (subst upred_sep_comm2_eq[of wsat])
apply (rule upred_entails_trans[OF _ upd_mono,OF _ except_zero_sepR])
apply (auto intro!: upred_entails_trans[OF _ upd_frameL] upred_frame)
apply (rule upred_wand_holdsE)
apply (subst upred_sep_comm)
apply (rule upred_entails_wand_holdsR[OF _ ownI_alloc[of "\<lambda>i. i \<in>\<^sub>d dnames N"], 
    OF _ allI[OF fresh_inv_name, of id, simplified]])
apply (rule upd_mono)
apply (auto intro!: upred_existsE')
apply (subst upred_sep_comm[of wsat])
apply (subst upred_sep_comm2_eq)
apply (auto intro!: upred_entails_trans[OF _ except_zeroI] upred_frame)
unfolding inv_raw_def
subgoal for i
apply (rule upred_existsI[of _ _ i])
apply (subst upred_sep_comm)
by (auto simp: dnames_def intro!:upred_pure_impl upred_entails_conjI upred_pureI)
done

lemma inv_raw_alloc_open: "dnames N \<subseteq>\<^sub>d E \<Longrightarrow>
  \<Turnstile>{E, E-dnames N}=> (inv_raw N P \<^emph> ((\<triangleright>P) ={E-dnames N, E}=\<^emph> upred_emp))"
unfolding fancy_upd_def
apply (rule upred_wand_holdsI)
apply (rule upred_wandE)
apply (rule upred_entails_trans[OF upred_wand_holdsE[OF ownI_alloc_open[of "\<lambda>i. i \<in>\<^sub>d dnames N"]],
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
apply (rule split_trans[of _ "ownE E \<^emph> ownI i P" "(ownE (DSet {i}) -\<^emph> wsat) \<^emph> ownD (DFSet {|i|}) \<^emph> ownI i P" 
  "ownE (DSet {i}) \<^emph> ownE (dnames N - DSet {i}) \<^emph> ownE (E - dnames N)", unfolded upred_sep_assoc_eq])
apply(rule can_be_split_R_R[OF persistent_dupl_split[OF persistent_ownI], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm2L]])
apply (auto simp: delem_dsubs dsubs_op_minus[symmetric] intro!: upred_entails_substI[OF 
    upred_entail_eqL[OF ownE_op_minus], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm]])
apply (auto simp: delem_dsubs dsubs_op_minus[symmetric] upred_weakeningL upred_sep_assoc_eq
  intro!: upred_entails_trans[OF _ upred_entail_eqL[OF ownE_op_minus], unfolded upred_sep_assoc_eq] 
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
apply (rule split_frame[of _ "ownE (DSet {i}) \<^emph> (ownE (DSet {i}) -\<^emph> wsat) \<^emph> ownI i P" 
  "ownE (dnames N - DSet {i}) \<^emph> ownD (DFSet {|i|})\<^emph> ownI i P" _ wsat
  "inv_raw N P \<^emph> ((\<triangleright>P) -\<^emph> (wsat \<^emph> ownE (E - dnames N)) ==\<^emph> \<diamondop>(wsat \<^emph> ownE E \<^emph> upred_emp))", 
  unfolded upred_sep_assoc_eq])
apply (rule can_be_split_mono[OF _ persistent_dupl_split[OF persistent_ownI], unfolded upred_sep_assoc_eq])
apply (rule can_be_split_rev)
apply (rule can_be_split_refl)
subgoal unfolding can_be_split_def by (simp add: upred_entails_eq_eq upred_sep_assoc_eq)
apply (auto intro: upred_entails_trans[OF upred_weakeningL] upred_wand_apply)
apply (rule split_frame[of _ "ownI i P" _ _ "inv_raw N P"])
apply (rule can_be_split_rev)
apply (rule persistent_dupl_split, pers_solver)
apply (rule can_be_split_refl)
apply (auto simp: inv_raw_def delem_dsubs upred_true_conj' upred_sep_assoc_eq intro!: upred_existsI[of _ _ i] upred_wandI)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]]; simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_substE[OF ownI_close, unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: dsubs_op_minus[symmetric] intro!: upred_entails_substE[OF 
    upred_entail_eqR[OF ownE_op_minus], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
by (auto simp: dsubs_op_minus[symmetric] upred_true_sep intro!: upred_entails_substE[OF 
    upred_entail_eqR[OF ownE_op_minus], unfolded upred_sep_assoc_eq] upred_entails_trans[OF _ updI]
    upred_entails_trans[OF _ except_zeroI])
done

lemma inv_raw_to_inv: "inv_raw N P -\<^emph> inv N P"
unfolding inv_def
apply (auto intro!: upred_wand_holdsI upred_entails_trans[OF _ upred_entail_eqL[OF pers_forall]] 
  upred_forallI upred_entails_trans[OF _ upred_entail_eqR[OF upred_pers_impl_pure]] upred_implI_pure)
subgoal for E
apply (rule add_holds[OF inv_raw_acc[of N E P]], assumption)
apply (auto intro!: upred_entails_trans[OF upred_wand_apply])
apply (auto intro!: upred_entails_trans[OF fupd_mono[OF upred_wand_apply]] 
  upred_entails_trans[OF upred_holds_entails'[OF fupd_mask_subseteq[of "E-dnames N" E]]])
using dsubs_dset apply fastforce
using upred_pers_mono[OF fupd_mono[OF upred_wand_apply]]
sorry
done

text \<open>
  The follow lemmata are the public API for invariants and should be enough to handle most proofs
  with invariants.
\<close>

lemma persistent_inv [pers_rule]: "persistent (inv N P)"
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
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_substE[OF upred_persisE] fupd_frame_mono)
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
  by (auto intro!: upred_wand_holdsI upred_entails_trans[OF _ fupd_mono[OF upred_wand_holdsE[OF 
    inv_raw_to_inv]]] upred_wand_holdsE[OF inv_raw_alloc])

lemma inv_alloc_open: "dnames N \<subseteq>\<^sub>d E \<Longrightarrow>
  \<Turnstile>{E, E-dnames N}=> (inv N P \<^emph> ((\<triangleright>P) ={E-dnames N, E}=\<^emph> upred_emp))"
apply (auto simp: upred_holds_entails)
apply (rule add_holds[OF inv_raw_alloc_open[of N E P]], simp)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF upred_weakeningL])
by (auto simp: upred_wand_holdsE[OF inv_raw_to_inv] intro!: fupd_mono upred_sep_mono)

lemma inv_acc: "dnames N \<subseteq>\<^sub>d E \<Longrightarrow> 
  ((inv N P) ={E, E-(dnames N)}=\<^emph> ((\<triangleright>P) \<^emph> ((\<triangleright>P) ={E-(dnames N), E}=\<^emph> \<upharpoonleft>True)))"
  by (auto simp: inv_def intro!: upred_wand_holdsI upred_entails_trans[OF upred_persisE]
    upred_entails_trans[OF upred_forall_inst[of _ E]] upred_entails_trans[OF upred_entail_eqL[OF upred_emp_impl]])

subsubsection \<open>Cancelable Invariants\<close>
type_synonym cinvG = frac
definition cinv_own :: "frac \<Rightarrow> iprop" where "cinv_own p = Own (constr_cinv (Some p))"
definition cinv :: "namespace \<Rightarrow> iprop \<Rightarrow> iprop" where "cinv N P = inv N (P \<or>\<^sub>u cinv_own 1)"

lemma cinv_persistent: "persistent (cinv N P)"
  unfolding cinv_def by (rule persistent_inv)

lemma timeless_cinv_own: "timeless (cinv_own p)"
  unfolding timeless_def cinv_own_def constr_cinv_def except_zero_def
  by transfer (simp add: n_incl_incl)

lemma cinv_own_valid: "upred_holds (cinv_own q1 -\<^emph> cinv_own q2 -\<^emph> \<upharpoonleft>(q1\<cdot>q2\<le>1))"
unfolding cinv_own_def
apply (rule upred_entails_wand_holdsR2[OF _ own_valid2])
apply (simp add: constr_cinv_def op_prod_def \<epsilon>_left_id op_option_def)
apply (simp add: upred_entails.rep_eq upred_valid.rep_eq upred_pure.rep_eq prod_n_valid_def \<epsilon>_n_valid)
apply (simp add: valid_raw_option_def valid_frac[symmetric] split: option.splits)
by (metis dcamera_valid_iff less_eq_frac.rep_eq one_frac.rep_eq valid_raw_frac.rep_eq)

lemma cinv_own_1_l: "upred_holds (cinv_own 1 -\<^emph> cinv_own q -\<^emph> \<upharpoonleft>False)"
proof (rule upred_wand_holds2I)
  from one_op have "(1\<cdot>q \<le> 1) \<longleftrightarrow> False" by (simp add: less_le_not_le)
  with upred_wand_holds2E[OF cinv_own_valid, of 1 q] show "cinv_own 1 \<^emph> cinv_own q \<turnstile> \<upharpoonleft>False" by simp
qed
end