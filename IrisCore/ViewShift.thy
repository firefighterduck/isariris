theory ViewShift
imports WorldSatisfaction Automation
begin

subsubsection \<open>Fancy updates\<close>
text \<open>
  Fancy updates describe steps between different sets of opened/closed invariants and are thus
  the basis for the impredicative invariant API.
\<close>

type_synonym mask = "name set"

context 
fixes get_inv :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> inv option"
  and put_inv
assumes inv_inG: "inG get_inv put_inv"
begin

abbreviation wsat :: "'res upred_f" where "wsat \<equiv> WorldSatisfaction.wsat put_inv"
abbreviation ownE :: "mask \<Rightarrow> 'res upred_f" where "ownE \<equiv> WorldSatisfaction.ownE put_inv"

definition fancy_upd :: "mask \<Rightarrow> mask \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("\<Turnstile>{_,_}=>_") where
  "\<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>P \<equiv> (wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P)))"
abbreviation wand_fupd ("_={_,_}=\<^emph>_") where "wand_fupd P \<E>\<^sub>1 \<E>\<^sub>2 Q \<equiv> P -\<^emph> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>Q"
  
abbreviation linear_fupd :: "mask \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("\<Turnstile>{_}=>_") where 
  "linear_fupd \<E> P \<equiv> \<Turnstile>{\<E>,\<E>}=>P"
abbreviation wand_linear_fupd ("_={_}=\<^emph>_") where "wand_linear_fupd P \<E> Q \<equiv> P -\<^emph> \<Turnstile>{\<E>}=>Q"

definition view_shift :: "'res upred_f \<Rightarrow> mask \<Rightarrow> mask \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("_ ={_,_}=>_")  where
  "view_shift P \<E>\<^sub>1 \<E>\<^sub>2 Q = \<box>(P -\<^emph> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>Q)"
abbreviation linear_vs :: "'res upred_f \<Rightarrow> mask \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("_ ={_}=>_") where
  "linear_vs P \<E> Q \<equiv> P ={\<E>,\<E>}=> Q"

lemma fupd_ne [upred_ne_rule]: "\<lbrakk>n_equiv n E1 E2; n_equiv n E3 E4; n_equiv n P Q\<rbrakk> \<Longrightarrow>
  n_equiv n (\<Turnstile>{E1, E3}=>P) (\<Turnstile>{E2, E4}=>Q)"
  apply (auto simp: fancy_upd_def ofe_refl intro!: upred_ne_rule)
  by (rule inv_inG)+

lemma vs_ne [upred_ne_rule]: "\<lbrakk>n_equiv n E1 E2; n_equiv n E3 E4; n_equiv n P Q; n_equiv n R S\<rbrakk> \<Longrightarrow>
  n_equiv n (P={E1, E3}=>R) (Q={E2, E4}=>S)"
  by (auto simp: view_shift_def intro: upred_ne_rule)
  
lemma fupd_mono: "P\<turnstile>Q \<Longrightarrow> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>P \<turnstile> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>Q"
proof -
  assume assm: "P\<turnstile>Q"
  have "\<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>P \<turnstile> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>P" by (rule upred_entails_refl)
  then have "((wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P)))) \<turnstile>
    ((wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P))))" by (simp add: fancy_upd_def)
  then have "((wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P)))) \<^emph> (wsat \<^emph> ownE \<E>\<^sub>1) \<turnstile>
    \<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P))" by (rule upred_wandE)
  then have "((wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P)))) \<^emph> (wsat \<^emph> ownE \<E>\<^sub>1) \<turnstile>
    \<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> Q))" 
    by (rule upred_entails_trans[OF _ upd_mono[OF except_zero_mono[OF upred_sep_mono[OF 
        upred_entails_refl]], OF assm]])
  then have "((wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P)))) \<turnstile>
    ((wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> Q))))" by (rule upred_wandI)
  then show ?thesis by (simp add: fancy_upd_def)
qed  

lemma fupd_empty: "P \<turnstile> \<Turnstile>{ {} }=>P"
apply (auto simp: fancy_upd_def intro!: upred_wandI upred_entails_trans[OF _ updI]
  upred_entails_trans[OF _ except_zeroI])
apply (subst upred_sep_comm)
by simp

lemma fupd_frame_r: "((\<Turnstile>{E1,E2}=> P) \<^emph> R) ={E1,E2}=\<^emph> (P \<^emph> R)"
apply (rule upred_wand_holdsI)
unfolding fancy_upd_def
apply (auto simp: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_wandI)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto intro!: upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq] 
  upd_mono_ext except_zero_mono_ext)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
by auto

lemma fupd_frame_l: "((\<Turnstile>{E1,E2}=> R) \<^emph> P) ={E1,E2}=\<^emph> (P \<^emph> R)"
  apply (subst (2) upred_sep_comm)
  by (rule fupd_frame_r)

lemma fupd_frame_split:  "can_be_split P P1 P2 \<Longrightarrow> ((\<Turnstile>{E1,E2}=> P1) \<^emph> P2) ={E1,E2}=\<^emph> P"
  unfolding can_be_split_def 
  using fupd_frame_r fupd_mono upred_entail_eqR upred_entails_wand_holdsR by blast
  
lemma fupd_frame_mono: "R\<^emph>P\<turnstile>Q \<Longrightarrow> R \<^emph> (\<Turnstile>{E1,E2}=> P) \<turnstile> \<Turnstile>{E1,E2}=> Q"
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (auto intro!: upred_entails_trans[OF upred_wand_holdsE[OF fupd_frame_r]] fupd_mono)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
by simp

lemma fupd_mask_subseteq: "E2 \<subseteq> E1 \<Longrightarrow> \<Turnstile>{E1,E2}=>\<Turnstile>{E2,E1}=>upred_emp"
proof -
  assume assm: "E2 \<subseteq> E1"
  then have e1: "E1 = (E1-E2)\<union>E2" by auto
  with assm have own_e1: "ownE E1 \<stileturn>\<turnstile> ownE (E1-E2) \<^emph> ownE E2" using ownE_op_minus[OF inv_inG]
    by (metis sup_commute upred_sep_comm)
  show ?thesis unfolding fancy_upd_def
  apply (rule upred_wand_holdsI)
  apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_substE[OF upred_entail_eqL[OF own_e1]]
    upred_entails_trans[OF _ updI] upred_entails_trans[OF _ except_zeroI])
  apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
  apply (rule upred_frame)
  apply (auto simp: upred_sep_assoc_eq intro!: upred_sep_mono upred_wandI)
  apply (auto intro!: upred_entails_trans[OF _ updI] upred_entails_trans[OF _ except_zeroI])
  apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
  apply (rule upred_entails_trans[OF upred_sep_comm2R])
  by (auto simp: upred_true_sep Un_absorb1 assm intro!: upred_entails_substE[OF 
      upred_entail_eqR[OF ownE_op_minus[OF inv_inG assm]], unfolded upred_sep_assoc_eq])
qed

lemma fupd_mask_trans: "\<Turnstile>{E1,E2}=>\<Turnstile>{E2,E3}=>P \<turnstile> \<Turnstile>{E1,E3}=>P"
unfolding fancy_upd_def
apply (rule upred_wandI)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (auto intro!: upred_entails_trans[OF upred_wand_apply] upred_entails_trans[OF upd_mono[OF 
    except_zero_mono[OF upred_wand_apply]]] upred_entails_trans[OF upd_mono[OF except_zero_bupd]]
    upred_entails_trans[OF upd_idem])
by (auto intro!: upd_mono except_zero_idem)

lemma fupd_mask_intro_subseteq: "E2 \<subseteq> E1 \<Longrightarrow> P \<turnstile> \<Turnstile>{E1,E2}=>\<Turnstile>{E2,E1}=>P"
apply (rule add_holds[OF fupd_mask_subseteq], assumption)
by (auto simp: upred_weakeningL intro!: fupd_frame_mono)

lemma fupd_intro: "P ={E}=\<^emph> P"
  by (auto intro: upred_wand_holdsI upred_entails_trans[OF fupd_mask_intro_subseteq[of E E]] fupd_mask_trans)

lemma fupd_intro': "P\<turnstile>Q \<Longrightarrow> P ={E}=\<^emph> Q"
  by (simp add: fupd_intro upred_entails_wand_holdsL)

lemma fupd_mask_weaken: "E2 \<subseteq> E1 \<Longrightarrow> ((\<Turnstile>{E2,E1}=> upred_emp) ={E2,E3}=\<^emph> P) -\<^emph> \<Turnstile>{E1,E3}=> P"
apply (rule upred_wand_holdsI)
apply (rule add_holds[OF fupd_mask_subseteq], assumption)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
by (auto intro!: upred_entails_trans[OF upred_wand_holdsE[OF fupd_frame_r]]
  upred_entails_trans[OF fupd_mono[OF upred_wand_apply]] upred_entails_trans[OF fupd_mask_trans])

lemma fupd_mask_intro: "E2 \<subseteq> E1 \<Longrightarrow> ((\<Turnstile>{E2,E1}=> upred_emp) -\<^emph> P) -\<^emph> \<Turnstile>{E1,E2}=> P"
apply (rule upred_wand_holdsI)
apply (auto intro!: upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_mask_weaken[of E2]]])
apply (auto intro!: upred_wandI upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_intro]])
by (auto intro: upred_wandE)

lemma persistent_vs [pers_rule,log_prog_rule]: "persistent (P ={E1,E2}=> Q)"
  unfolding view_shift_def by pers_solver

lemma timeless_later_vs: "timeless P \<Longrightarrow> (\<triangleright>P) ={E}=> P"
  unfolding timeless_def view_shift_def fancy_upd_def
  apply (subst upred_holds_entails)
  by (smt (verit, ccfv_SIG) except_zero_sepL persistent_persisI persistent_pure updI 
    upred_entails_substE upred_entails_trans upred_holds_entails upred_sep_comm upred_wand_holds2I)

lemma is_except_zero_fupd [iez_rule,log_prog_rule]: "is_except_zero (\<Turnstile>{E1,E2}=> P)"
  unfolding is_except_zero_def fancy_upd_def
  apply (subst except_zero_def)
  apply (rule upred_disjE)
  apply (rule upred_wandI)
  apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
  apply (rule upred_wand_apply)
  by (metis (no_types, opaque_lifting) bupd_emp except_zero_def upd_mono_ext upred_disjIR 
    upred_true_sep upred_wandI upred_weakeningL)

lemma fupd_ext: "(\<Turnstile>{E1,E2}=>P) \<turnstile> (P={E2,E3}=\<^emph>Q)={E1,E3}=\<^emph>Q"
  apply (rule upred_wandI)
  apply (subst upred_sep_comm)
  apply (rule upred_entails_trans[OF fupd_frame_mono[OF upred_entails_trans[OF upred_entails_eq[OF 
    upred_sep_comm] upred_wand_apply]]])
  by (auto intro: upred_entails_trans[OF fupd_mask_trans])

lemma fupd_mask_frameR': "E1 \<inter> Ef = {} \<Longrightarrow> (\<Turnstile>{E1,E2}=> ((\<upharpoonleft>(E2 \<inter> Ef = {})) \<longrightarrow>\<^sub>u P)) ={E1\<union>Ef,E2\<union>Ef}=\<^emph>P"
apply (rule upred_wand_holdsI)
unfolding fancy_upd_def
apply (auto simp: upred_sep_assoc_eq intro!: upred_wandI upred_entails_substE[OF upred_entail_eqL[OF ownE_op[OF inv_inG]]])
apply (subst upred_sep_assoc_eq[symmetric, of _ wsat "ownE E1"])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
apply (auto simp: upred_sep_assoc_eq intro!: upd_mono_ext except_zero_mono_ext)
apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF _ upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_frame)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_substE[OF upred_entail_eqR[OF ownE_op'[OF inv_inG]]])
apply (rule upred_entails_substE[OF upred_entail_eqR[OF upred_pure_sep_conj]])
apply (subst upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_substE[OF upred_entail_eqL[OF upred_pure_sep_conj], unfolded upred_sep_assoc_eq])
by (auto intro: upred_entails_substE[OF upred_impl_apply])

lemma fupd_mask_frameR: "E1 \<inter> Ef = {} \<Longrightarrow> (\<Turnstile>{E1,E2}=> P) ={E1\<union>Ef,E2\<union>Ef}=\<^emph>P"
apply (rule upred_wand_holdsI)
by (auto intro!: upred_entails_trans[OF _ upred_wand_holdsE[OF fupd_mask_frameR']] fupd_mono upred_implI_pure)

lemma fupd_mask_mono: "E1 \<subseteq> E2 \<Longrightarrow> (\<Turnstile>{E1}=>P) ={E2}=\<^emph>P"
proof -
  assume assm: "E1 \<subseteq> E2"
  then have "E1\<union>E2 = E2" by auto
  then have "E1 \<inter> (E2-E1) = {}" by simp
  from fupd_mask_frameR[OF this, of E1 P, simplified, unfolded \<open>E1\<union>E2 = E2\<close>]
  show ?thesis .
qed

lemma fupd_plainly_mask_emp: "(\<Turnstile>{E,{}}=> \<^item> P) \<turnstile> \<Turnstile>{E}=> P"
unfolding fancy_upd_def
apply iIntros
apply (iAssert_pers "\<diamondop>\<^item>P")
subgoal apply (check_moveL "?p-\<^emph>?q") apply iApply_wand
apply (entails_substR rule: bupd_plain) prefer 2 apply plain_solver
apply (rule upd_mono)
apply (rule except_zero_mono)
by iFrame_single
apply (entails_substR rule: except_zero_bupd)
apply (rule except_zero_mono_ext)
apply (entails_substR rule: updI)
apply (check_moveR "ownE E") apply iFrame_single
apply (check_moveR wsat) apply iFrame_single
apply (iApply rule: upred_plainE) by iFrame_single

lemma fupd_mask_intro_discard: "E2 \<subseteq> E1 \<Longrightarrow> P \<turnstile> \<Turnstile>{E1,E2}=>P"
by (meson add_holds fupd_frame_mono fupd_mask_subseteq upred_weakeningL)

lemma fupd_frameR : "frame P Q R \<Longrightarrow> frame (\<Turnstile>{E1,E2}=>P) Q (\<Turnstile>{E1,E2}=>R)"
  unfolding frame_def by (rule fupd_frame_mono)

lemma fupd_frame_refl [frame_rule,log_prog_rule]: "frame P Q R \<Longrightarrow> frame (\<Turnstile>{E1,E2}=>P) (\<Turnstile>{E3,E2}=>Q) (\<Turnstile>{E1,E3}=>R)"
  unfolding frame_def
  apply (entails_substR rule: fupd_mask_trans)
  apply (iApply rule: fupd_frame_mono)+
  by (simp add: upred_sep_comm)

lemma fupd_frame_refl' [frame_rule,log_prog_rule]: "frame P Q R \<Longrightarrow> frame (\<Turnstile>{E1,E2}=>P) (\<Turnstile>{E1,E3}=>Q) (\<Turnstile>{E3,E2}=>R)"
  using frame_rev fupd_frame_refl by blast

lemma fupd_frameL [frame_rule,log_prog_rule]: "frame P Q R \<Longrightarrow> frame (\<Turnstile>{E1,E2}=>P) (\<Turnstile>{E1,E2}=>Q) R"
  unfolding frame_def using fupd_frame_mono by (simp add: upred_sep_comm)
  
lemma upd_fupd: "(\<Rrightarrow>\<^sub>b P) ={E}=\<^emph> P"
unfolding fancy_upd_def
apply iIntro
apply (entails_substL rule: upd_frameL)
apply (subst upred_sep_assoc_eq)
apply (rule upd_mono)
apply (entails_substR rule: except_zeroI)
by iFrame_single+

lemma elim_modal_fupd: "elim_modal (\<Turnstile>{E1,E2}=>P) P (\<Turnstile>{E1,E3}=>Q) (\<Turnstile>{E2,E3}=>Q)"
  unfolding elim_modal_def by (simp add: fupd_ext upred_wandE)

lemma elim_modal_upd: "elim_modal (\<Rrightarrow>\<^sub>b P) P (\<Turnstile>{E1,E2}=>Q) (\<Turnstile>{E1,E2}=>Q)"
  unfolding elim_modal_def using upd_fupd elim_modal_fupd[unfolded elim_modal_def]
  using fupd_ext upred_entails_wand_holdsR upred_wand_holds2E by blast

lemma fupd_plainly_mask: "(\<Turnstile>{E,E'}=> \<^item> P) \<turnstile> \<Turnstile>{E}=> P"
apply (entails_substR rule: fupd_plainly_mask_emp)
apply (rule elim_modal_entails) apply (rule elim_modal_fupd)
by (entails_substR rule: fupd_mask_intro_discard[OF empty_subsetI])

lemma fupd_plain_mask_emp: "plain P \<Longrightarrow> (\<Turnstile>{E,{}}=> P) \<turnstile> \<Turnstile>{E}=> P"
apply (entails_substR rule: fupd_plainly_mask_emp)
apply (rule fupd_mono) unfolding plain_def by assumption

lemma fupd_plain_mask: "plain P \<Longrightarrow> (\<Turnstile>{E,E'}=> P) \<turnstile> \<Turnstile>{E}=> P"
apply (entails_substR rule: fupd_plainly_mask)
apply (rule fupd_mono) unfolding plain_def by assumption

lemma fupd_trans_frame: "((Q ={E2,E3}=\<^emph> upred_emp) \<^emph> \<Turnstile>{E1,E2}=> (Q\<^emph>P)) ={E1,E3}=\<^emph> P"
proof -
  have "\<Turnstile>{E1,E3}=>P \<turnstile> \<Turnstile>{E1,E3}=>P" by simp
  then have "\<Turnstile>{E1,E3}=>(P \<^emph> upred_emp) \<turnstile> \<Turnstile>{E1,E3}=>P"
    by (simp add: emp_rule)
  then have "\<Turnstile>{E1,E2}=>\<Turnstile>{E2,E3}=>(P \<^emph> upred_emp) \<turnstile> \<Turnstile>{E1,E3}=>P"
    using fupd_mask_trans upred_entails_trans by blast
  then have "\<Turnstile>{E1,E2}=>(P \<^emph> (\<Turnstile>{E2,E3}=>upred_emp)) \<turnstile> \<Turnstile>{E1,E3}=>P"
    using fupd_frame_mono fupd_mono upred_entails_refl upred_entails_trans by blast
  then have "\<Turnstile>{E1,E2}=>(P \<^emph> (Q\<^emph>(Q={E2,E3}=\<^emph>upred_emp))) \<turnstile> \<Turnstile>{E1,E3}=>P"
    by (meson fupd_mono upred_entails_trans upred_frameL upred_wand_apply)
  then have "(\<Turnstile>{E1,E2}=>(P \<^emph> Q)) \<^emph> (Q={E2,E3}=\<^emph>upred_emp) \<turnstile> \<Turnstile>{E1,E3}=>P"
    by (simp add: fupd_frame_r upred_entails_wand_holdsR upred_sep_assoc_eq upred_wand_holdsE)
  then show ?thesis apply - apply iIntro
  by (simp add: upred_sep_comm)
qed

lemma fupd_exists_lift: "(\<exists>\<^sub>u x. \<Turnstile>{E1,E2}=>(P x)) \<turnstile> \<Turnstile>{E1,E2}=>(\<exists>\<^sub>u x. P x)"
  by (meson fupd_mono upred_entails_refl upred_existsE_eq)

lemma fupd_forall: "(\<Turnstile>{E1,E2}=> (\<forall>\<^sub>ux. P x)) \<turnstile> (\<forall>\<^sub>ux. (\<Turnstile>{E1,E2}=> P x))"
by (simp add: fupd_mono upred_forallI upred_forall_inst)

lemma fupd_plainly_forall: "(\<forall>\<^sub>ux. (\<Turnstile>{E}=> \<^item> P x)) \<turnstile> (\<Turnstile>{E}=> (\<forall>\<^sub>ux. P x))"
unfolding fancy_upd_def
apply iIntros
apply (iAssert_pers "\<diamondop> \<^item> (\<forall>\<^sub>ux. P x)")
subgoal
apply (entails_substR rule: except_zero_mono[OF upred_plain_forall'])
apply (entails_substR rule: upred_ez_forall')
apply iForallR subgoal for x apply (iForallL x)
apply iApply_wand
apply (entails_substR rule: bupd_plain) prefer 2 apply plain_solver
apply (rule upd_mono)
apply (rule except_zero_mono)
by iFrame_single done
apply (entails_substR rule: except_zero_bupd)
apply (rule except_zero_mono_ext)
apply (entails_substR rule: updI)
apply (check_moveR "ownE E") apply iFrame_single
apply (check_moveR wsat) apply iFrame_single
apply iForallR subgoal for x
apply (entails_substL rule: upred_plain_forall)
apply (iForallL x) 
apply (iApply rule: upred_plainE) by iFrame_single done

lemma fupd_plain_forall2: "(\<And>x. plain (P x)) \<Longrightarrow> (\<forall>\<^sub>ux. (\<Turnstile>{E}=> P x)) \<turnstile> (\<Turnstile>{E}=> (\<forall>\<^sub>ux. P x))"
apply (entails_substR rule: fupd_plainly_forall)
apply iForallR subgoal for x apply (iForallL x)
apply (rule fupd_mono) unfolding plain_def by assumption done

lemma fupd_plain_forall: "\<lbrakk>\<And>x. plain (P x); E2\<subseteq>E1\<rbrakk> \<Longrightarrow>
  (\<Turnstile>{E1,E2}=> (\<forall>\<^sub>ux. P x)) \<stileturn>\<turnstile> (\<forall>\<^sub>ux. (\<Turnstile>{E1,E2}=> P x))"
apply (auto simp: upred_entail_eq_def)
subgoal by (rule fupd_forall)
  apply (rule upred_entails_trans[where ?Q ="\<forall>\<^sub>ux. \<Turnstile>{E1}=> P x"])
subgoal apply (rule upred_forall_mono) by (rule fupd_plain_mask)
  apply (iApply rule: fupd_plain_forall2)
  apply (rule elim_modal_entails) apply (rule elim_modal_fupd)
  apply (iApply rule: plainE, log_prog_solver) apply (iDrop "upred_forall ?p")+
  apply (iApply rule: fupd_mask_intro_discard[of E2 E1]) apply (iDrop "\<^item> ?p")
  apply (rule fupd_mono)
  by (rule upred_plainE)

lemma elim_acc_fupd: "elim_acc (fancy_upd E1 E2) (fancy_upd E2 E1) a b c (\<Turnstile>{E1,E}=>Q) (\<lambda>x. \<Turnstile>{E2}=> (b x \<^emph> 
  (case c x of Some P \<Rightarrow> (P -\<^emph> (\<Turnstile>{E1,E}=>Q)) | None \<Rightarrow> \<Turnstile>{E1,E}=>Q)))"
  apply (auto simp: elim_acc_def accessor_def)
  apply (rule elim_modal_entails'[OF elim_modal_fupd])
  apply iIntros subgoal for x
  apply (iForallL x) 
  apply iApply_wand
  apply (rule elim_modal_entails'[OF elim_modal_fupd]) apply iris_simp
  apply iApply_wand
  apply (rule elim_modal_entails'[OF elim_modal_fupd])
  apply (cases "c x") apply (auto simp: iris_simp)
  by iApply_wand done
  
abbreviation fancy_step :: "mask \<Rightarrow> mask \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("\<Turnstile>{_}[_]\<triangleright>=>_") where
  "fancy_step Eo Ei Q \<equiv> \<Turnstile>{Eo,Ei}=> \<triangleright> \<Turnstile>{Ei,Eo}=> Q"
abbreviation fancy_wand_step :: "'res upred_f \<Rightarrow> mask \<Rightarrow> mask \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("_={_}[_]\<triangleright>=\<^emph>_") where
  "fancy_wand_step P Eo Ei Q \<equiv> P -\<^emph> \<Turnstile>{Eo}[Ei]\<triangleright>=> Q"
abbreviation fancy_linear_step :: "mask \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("\<Turnstile>{_}\<triangleright>=>_") where
  "fancy_linear_step E Q \<equiv> \<Turnstile>{E}[E]\<triangleright>=> Q"
abbreviation fancy_linear_wand_step :: "'res upred_f \<Rightarrow> mask \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("_={_}\<triangleright>=\<^emph>_") where
  "fancy_linear_wand_step P E Q \<equiv> P -\<^emph> \<Turnstile>{E}\<triangleright>=> Q"
abbreviation fancy_steps :: "mask \<Rightarrow> mask \<Rightarrow> nat \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("\<Turnstile>{_}[_]\<triangleright>^_=>_") where
  "fancy_steps Eo Ei n Q \<equiv> ((\<lambda>P. \<Turnstile>{Eo}[Ei]\<triangleright>=>P)^^n) Q"
abbreviation fancy_wand_steps :: "'res upred_f \<Rightarrow> mask \<Rightarrow> mask \<Rightarrow> nat \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("_={_}[_]\<triangleright>^_=\<^emph>_") 
  where "fancy_wand_steps P Eo Ei n Q \<equiv> P -\<^emph> (\<Turnstile>{Eo}[Ei]\<triangleright>^n=>Q)"
abbreviation fancy_linear_steps :: "mask \<Rightarrow> nat \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("\<Turnstile>{_}\<triangleright>^_=>_") where
  "fancy_linear_steps E n Q \<equiv> \<Turnstile>{E}[E]\<triangleright>^n=>Q"
abbreviation fancy_linear_wand_steps :: "'res upred_f \<Rightarrow> mask \<Rightarrow> nat \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" ("_={_}\<triangleright>^_=\<^emph>_") where
  "fancy_linear_wand_steps P E n Q \<equiv> P={E}[E]\<triangleright>^n=\<^emph>Q"

lemma step_fupdN_wand: "(\<Turnstile>{Eo}[Ei]\<triangleright>^n=> P) -\<^emph> (P -\<^emph> Q) -\<^emph> (\<Turnstile>{Eo}[Ei]\<triangleright>^n=> Q)"
proof (iIntro, induction n)
  case 0
  then show ?case by (auto intro: upred_wand_apply)
next
  case (Suc n)
  show ?case apply simp
  apply (rule upred_entails_trans[OF _ fupd_mono[OF upred_later_mono[OF fupd_mono[OF Suc]]]])
  apply (check_moveL "\<Turnstile>{?E1,?E2}=>?P", rule elim_modal_entails'[OF elim_modal_fupd])
  apply (rule upred_entails_trans[OF _ fupd_intro[to_entailment]])
  apply (rule upred_later_mono_extR)
  apply (rule framing, log_prog_solver)
  apply (rule upred_entails_trans[OF _ fupd_intro[to_entailment]])
  by iris_simp
qed
end
end