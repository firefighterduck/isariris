theory ViewShift
imports WorldSatisfaction
begin

subsubsection \<open>Fancy updates\<close>
text \<open>
  Fancy updates describe steps between different sets of opened/closed invariants and are thus
  the basis for the impredicative invariant API.
\<close>

type_synonym mask = "name set"

definition fancy_upd :: "mask \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("\<Turnstile>{_,_}=>_") where
  "\<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>P \<equiv> (wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P)))"
abbreviation wand_fupd ("_={_,_}=\<^emph>_") where "wand_fupd P \<E>\<^sub>1 \<E>\<^sub>2 Q \<equiv> P -\<^emph> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>Q"
  
abbreviation linear_fupd :: "mask \<Rightarrow> iprop \<Rightarrow> iprop" ("\<Turnstile>{_}=>_") where 
  "linear_fupd \<E> P \<equiv> \<Turnstile>{\<E>,\<E>}=>P"
abbreviation wand_linear_fupd ("_={_}=\<^emph>_") where "wand_linear_fupd P \<E> Q \<equiv> P -\<^emph> \<Turnstile>{\<E>}=>Q"

definition view_shift :: "iprop \<Rightarrow> mask \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("_ ={_,_}=>_")  where
  "view_shift P \<E>\<^sub>1 \<E>\<^sub>2 Q = \<box>(P -\<^emph> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>Q)"
abbreviation linear_vs :: "iprop \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("_ ={_}=>_") where
  "linear_vs P \<E> Q \<equiv> P ={\<E>,\<E>}=> Q"
  
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
  with assm have own_e1: "ownE E1 \<stileturn>\<turnstile> ownE (E1-E2) \<^emph> ownE E2" using ownE_op_minus
    by (metis inf_sup_aci(5) upred_sep_comm)  
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
      upred_entail_eqR[OF ownE_op_minus[OF assm]], unfolded upred_sep_assoc_eq])
qed

lemma fupd_mask_trans: " \<Turnstile>{E1,E2}=>\<Turnstile>{E2,E3}=>P \<turnstile> \<Turnstile>{E1,E3}=>P"
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

lemma persistent_vs [pers_rule]: "persistent (P ={E1,E2}=> Q)"
  unfolding view_shift_def by pers_solver

lemma fupd_ext: "(\<Turnstile>{E1,E2}=>P) \<turnstile> (P={E2,E3}=\<^emph>Q)={E1,E3}=\<^emph>Q"
  apply (rule upred_wandI)
  apply (subst upred_sep_comm)
  apply (rule upred_entails_trans[OF fupd_frame_mono[OF upred_entails_trans[OF upred_entails_eq[OF 
    upred_sep_comm] upred_wand_apply]]])
  by (auto intro: upred_entails_trans[OF fupd_mask_trans])

lemma fupd_mask_frameR': "E1 \<inter> Ef = {} \<Longrightarrow> (\<Turnstile>{E1,E2}=> ((\<upharpoonleft>(E2 \<inter> Ef = {})) \<longrightarrow>\<^sub>u P)) ={E1\<union>Ef,E2\<union>Ef}=\<^emph>P"
apply (rule upred_wand_holdsI)
unfolding fancy_upd_def
apply (auto simp: upred_sep_assoc_eq intro!: upred_wandI upred_entails_substE[OF upred_entail_eqL[OF ownE_op]])
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
apply (rule upred_entails_substE[OF upred_entail_eqR[OF ownE_op']])
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

lemma wp_fupd_helper: "\<forall>\<^sub>u v. (upred_emp ={E}=\<^emph> upred_emp)"
apply (subst upred_holds_entails)
apply (rule upred_forallI)
using fupd_intro upred_holds_entails by auto

abbreviation fancy_step :: "mask \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("\<Turnstile>{_}[_]\<triangleright>=>_") where
  "fancy_step Eo Ei Q \<equiv> \<Turnstile>{Eo,Ei}=> \<triangleright> \<Turnstile>{Ei,Eo}=> Q"
abbreviation fancy_wand_step :: "iprop \<Rightarrow> mask \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("_={_}[_]\<triangleright>=\<^emph>_") where
  "fancy_wand_step P Eo Ei Q \<equiv> P -\<^emph> \<Turnstile>{Eo}[Ei]\<triangleright>=> Q"
abbreviation fancy_linear_step :: "mask \<Rightarrow> iprop \<Rightarrow> iprop" ("\<Turnstile>{_}\<triangleright>=>_") where
  "fancy_linear_step E Q \<equiv> \<Turnstile>{E}[E]\<triangleright>=> Q"
abbreviation fancy_linear_wand_step :: "iprop \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("_={_}\<triangleright>=\<^emph>_") where
  "fancy_linear_wand_step P E Q \<equiv> P -\<^emph> \<Turnstile>{E}\<triangleright>=> Q"
abbreviation fancy_steps :: "mask \<Rightarrow> mask \<Rightarrow> nat \<Rightarrow> iprop \<Rightarrow> iprop" ("\<Turnstile>{_}[_]\<triangleright>^_=>_") where
  "fancy_steps Eo Ei n Q \<equiv> ((\<lambda>P. \<Turnstile>{Eo}[Ei]\<triangleright>=>P)^^n) Q"
abbreviation fancy_wand_steps :: "iprop \<Rightarrow> mask \<Rightarrow> mask \<Rightarrow> nat \<Rightarrow> iprop \<Rightarrow> iprop" ("_={_}[_]\<triangleright>^_=\<^emph>_") 
  where "fancy_wand_steps P Eo Ei n Q \<equiv> P -\<^emph> (\<Turnstile>{Eo}[Ei]\<triangleright>^n=>Q)"
abbreviation fancy_linear_steps :: "mask \<Rightarrow> nat \<Rightarrow> iprop \<Rightarrow> iprop" ("\<Turnstile>{_}\<triangleright>^_=>_") where
  "fancy_linear_steps E n Q \<equiv> \<Turnstile>{E}[E]\<triangleright>^n=>Q"
abbreviation fancy_linear_wand_steps :: "iprop \<Rightarrow> mask \<Rightarrow> nat \<Rightarrow> iprop \<Rightarrow> iprop" ("_={_}\<triangleright>^_=\<^emph>_") where
  "fancy_linear_wand_steps P E n Q \<equiv> P={E}[E]\<triangleright>^n=\<^emph>Q"
end