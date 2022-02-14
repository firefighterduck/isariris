theory ViewShift
imports Invariant
begin

subsubsection \<open>Fancy updates\<close>

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
unfolding fancy_upd_def
apply (rule upred_wandI)
unfolding wsat_def ownE_def ownD_def sep_map_set_def except_zero_def
sorry

text \<open>Semantic invariant definition\<close>
definition sinv :: "namespace \<Rightarrow> iprop \<Rightarrow> iprop" where
  "sinv N P = \<box>(\<forall>\<^sub>u E. ((\<upharpoonleft>((dnames N) \<subseteq>\<^sub>d E)) \<longrightarrow>\<^sub>u 
    ((\<Turnstile>{E,E-(dnames N)}=> (\<triangleright>P)) \<^emph> ((\<triangleright>P) ={E-(dnames N), E}=\<^emph> \<upharpoonleft>True))))"

lemma inv_acc: "dnames N \<subseteq>\<^sub>d E \<Longrightarrow> 
  ((inv N P) ={E, E-(dnames N)}=\<^emph> ((\<triangleright>P) \<^emph> ((\<triangleright>P) ={E-(dnames N), E}=\<^emph> \<upharpoonleft>True)))"
apply (auto simp: fancy_upd_def upred_sep_assoc_eq inv_def intro!: upred_wand_holdsI upred_existsE')
apply (rule upred_entails_trans[OF upred_entail_eqR[OF persistent_holds_sep']], pers_solver)
apply (auto intro!: upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]] upred_pure_impl)
apply (auto simp: upred_sep_assoc_eq intro!: upred_wandI)
apply (subst dsubs_op_minus[of "dnames N"], assumption)
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_exchange[OF upred_entail_eqL[OF ownE_op_minus]])
subgoal for i
unfolding delem_dsubs[of i "dnames N"]
apply (subst dsubs_op_minus[of "DSet {i}" "dnames N"], assumption)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: upred_sep_assoc_eq intro!: upred_entails_exchange[OF 
    upred_entail_eqL[OF ownE_op_minus], of "DSet {i}" "dnames N"] upred_entails_trans[OF _ updI]
    upred_entails_trans[OF _ except_zeroI])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm4_1])
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_exchange[OF upred_entail_eqR[OF persistent_dupl]])
apply pers_solver
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm3L])
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_exchange[OF ownI_open, unfolded upred_sep_assoc_eq])
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
apply (rule upred_entails_exchange[OF ownI_close, unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: dsubs_op_minus[symmetric] intro!: upred_entails_exchange[OF 
    upred_entail_eqR[OF ownE_op_minus], unfolded upred_sep_assoc_eq])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: dsubs_op_minus[symmetric] intro!: upred_entails_exchange[OF 
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

lemma inv_alloc: "(\<triangleright>P) ={E}=\<^emph> (inv N P)"
apply (auto simp: fancy_upd_def upred_sep_assoc_eq intro!: upred_wand_holdsI upred_wandI)
apply (subst upred_sep_comm2_eq[of wsat])
apply (rule upred_entails_trans[OF _ upd_mono,OF _ except_zero_sepR])
apply (auto intro!: upred_entails_trans[OF _ upd_frameL] upred_frame)
apply (rule upred_wand_holdsE)
apply (subst upred_sep_comm)
apply (rule upred_entails_wand_holdsR[OF _ ownI_alloc[of "\<lambda>i. i \<in>\<^sub>d dnames N"], OF _ allI[OF fresh_inv_name, of id, simplified]])
apply (rule upd_mono)
apply (auto intro!: upred_existsE')
apply (subst upred_sep_comm[of wsat])
apply (subst upred_sep_comm2_eq)
apply (auto intro!: upred_entails_trans[OF _ except_zeroI] upred_frame)
unfolding inv_def
subgoal for i
apply (rule upred_existsI[of _ _ i])
apply (subst upred_sep_comm)
by (auto simp: dnames_def intro!:upred_pure_impl upred_entails_conjI upred_pureI)
done
end