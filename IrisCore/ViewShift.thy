theory ViewShift
imports WorldSatisfaction
begin

subsubsection \<open>Fancy updates\<close>
text \<open>
  Fancy updates describe steps between different sets of opened/closed invariants and are thus
  the basis for the impredicative invariant API.
\<close>

type_synonym mask = "name dset"

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

lemma fupd_frame_mono: "R\<^emph>P\<turnstile>Q \<Longrightarrow> R \<^emph> (\<Turnstile>{E1,E2}=> P) \<turnstile> \<Turnstile>{E1,E2}=> Q"
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (auto intro!: upred_entails_trans[OF upred_wand_holdsE[OF fupd_frame_r]] fupd_mono)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
by simp


lemma fupd_mask_subseteq: "E2\<subseteq>\<^sub>dE1 \<Longrightarrow> \<Turnstile>{E1,E2}=>\<Turnstile>{E2,E1}=>upred_emp"
proof -
  assume assm: "E2 \<subseteq>\<^sub>d E1"
  then have e1: "E1 = (E1-E2)\<cdot>E2" by (simp add: camera_comm dsubs_op_minus)
  with assm have own_e1: "ownE E1 \<stileturn>\<turnstile> ownE (E1-E2) \<^emph> ownE E2" using ownE_op_minus
  by (metis dsubs_op_minus upred_sep_comm)
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
  by (auto simp: dsubs_op_minus[OF assm,symmetric] upred_true_sep intro!: upred_entails_substE[OF 
      upred_entail_eqR[OF ownE_op_minus[OF assm]], unfolded upred_sep_assoc_eq])
qed
  
lemma persistent_vs [pers_rule]: "persistent (P ={E1,E2}=> Q)"
  unfolding view_shift_def by pers_solver
end