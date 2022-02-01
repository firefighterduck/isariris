theory Invariant
imports DerivedConstructions BaseLogicShallow Frac AuthHeap Misc "../SpanningTree/SpanningTreeCameras"
  Namespace iPropShallow 
begin

subsection \<open> Invariants \<close>

text \<open>The modular invariant camera based on the heap camera\<close>
definition own_inv :: "inv \<Rightarrow> iprop" ("Own\<^sub>i _") where
  "own_inv i = Own(constr_inv i)"

context assumes "SORT_CONSTRAINT('c::ucamera)" and "SORT_CONSTRAINT('v::ofe)"
begin

text \<open>Allocate new invariant map\<close>
definition ownI :: "name \<Rightarrow> iprop \<Rightarrow> iprop" where
  "ownI \<iota> P = Own\<^sub>i (fragm [\<iota>\<mapsto>to_ag (Next (pre P))],\<epsilon>,\<epsilon>)"

definition inv :: "namespace \<Rightarrow> iprop \<Rightarrow>  iprop" where
  "inv N P \<equiv> \<exists>\<^sub>u \<iota>. ((\<upharpoonleft>(\<iota>\<in>names N)) \<and>\<^sub>u ownI \<iota> P)"
  
text \<open>Allocate new enabled invariant map\<close>
definition ownE :: "name dset \<Rightarrow> iprop" where
  "ownE E = Own\<^sub>i (\<epsilon>,E,\<epsilon>)"

text \<open>Allocate new disabled invariant map\<close>
definition ownD :: "name dfset \<Rightarrow> iprop" where
  "ownD D = Own\<^sub>i (\<epsilon>,\<epsilon>,D)"  
  
definition lift_inv_map :: "(name\<rightharpoonup>iprop) \<Rightarrow> (name\<rightharpoonup> pre_iprop later ag)" where
  "lift_inv_map = (\<circ>) (map_option (to_ag \<circ> Next \<circ> pre))"
  
text \<open>World satisfaction, i.e. the invariant that holds all invariants\<close>
definition wsat :: iprop where
  "wsat \<equiv> \<exists>\<^sub>u (I::name\<rightharpoonup>iprop).
    ((Own\<^sub>i(full(lift_inv_map I),\<epsilon>,\<epsilon>))
    \<^emph> (sep_map_set (\<lambda>\<iota>. ((\<triangleright>((the \<circ> I) \<iota>)) \<^emph> ownD (DFSet {|\<iota>|})) \<or>\<^sub>u (ownE (DSet {\<iota>}))) (dom I))
  )"
end

lemma persistent_ownI: "persistent (ownI \<iota> P)"
  unfolding ownI_def own_inv_def by (rule persistent_core_own2)
  (auto simp add: prod_pcore_id_pred \<epsilon>_pcore_id_def fragm_core_id constr_inv_def 
      simp del: \<epsilon>_dfset_def \<epsilon>_dset_def \<epsilon>_option_def)

lemma persistent_inv: "persistent (inv N P)"
  unfolding inv_def
  apply (rule persistent_exists)
  apply (rule allI)
  apply (rule persistent_conj)
  apply (rule persistent_pure)
  by (rule persistent_ownI)

lemma "(\<forall>n x. (\<forall>i\<in>dom f. f i = m i) \<longrightarrow> Rep_upred_f P x n) \<Longrightarrow> 
  \<V>(constr_inv (full m,\<epsilon>,\<epsilon>) \<cdot> constr_inv (fragm f,\<epsilon>,\<epsilon>)) \<turnstile> P"
  apply transfer
  unfolding constr_inv_def
  apply (simp add: op_prod_def auth_comb_opL \<epsilon>_left_id del: \<epsilon>_dfset_def \<epsilon>_dset_def \<epsilon>_option_def)
  apply (simp add:  prod_n_valid_def \<epsilon>_n_valid valid_raw_option_def del: \<epsilon>_dfset_def \<epsilon>_dset_def)
  
  
lemma auth_map_both_validI: 
  "\<V>(constr_inv (full m,\<epsilon>,\<epsilon>) \<cdot> constr_inv (fragm [k\<mapsto>v],\<epsilon>,\<epsilon>)) \<turnstile> (m k =\<^sub>u Some v)"
unfolding constr_inv_def op_prod_def
apply (simp add: \<epsilon>_left_id auth_comb_opL del: \<epsilon>_dfset_def \<epsilon>_dset_def \<epsilon>_option_def split: prod.splits)
apply (simp add: op_fun_def op_option_def del: \<epsilon>_dfset_def \<epsilon>_dset_def)
apply transfer
apply (simp add: prod_n_valid_def \<epsilon>_n_valid valid_raw_option_def del: \<epsilon>_dfset_def \<epsilon>_dset_def)


lemma invariant_lookup: 
  "Own\<^sub>i (full (lift_inv_map I),\<epsilon>,\<epsilon>) \<^emph> ownI \<iota> P \<turnstile> (\<exists>\<^sub>u Q. \<upharpoonleft>(I \<iota> = Some Q) \<^emph> \<triangleright> (Q=\<^sub>uP))"
  unfolding ownI_def own_inv_def
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF own_op]])
  apply (rule upred_entails_trans[OF own_valid])
  
subsubsection \<open>Cancelable Invariants\<close>
type_synonym cinvG = frac
definition cinv_own :: "frac \<Rightarrow> iprop" where "cinv_own p = Own (constr_cinv (Some p))"
definition cinv :: "namespace \<Rightarrow> iprop \<Rightarrow> iprop" where "cinv N P = inv N (P \<or>\<^sub>u cinv_own 1)"

lemma cinv_persistent: "persistent (cinv N P)"
  unfolding cinv_def by (rule persistent_inv)

lemma timeless_cinv_own: "timeless (cinv_own p)"
unfolding timeless_def cinv_own_def constr_cinv_def except_zero_def
apply transfer
by (simp add: n_incl_incl del: \<epsilon>_dfset_def \<epsilon>_dset_def)

lemma cinv_own_valid: "upred_holds (cinv_own q1 -\<^emph> cinv_own q2 -\<^emph> \<upharpoonleft>(q1\<cdot>q2\<le>1))"
unfolding cinv_own_def
apply (rule upred_entails_wand_holdsR2[OF _ own_valid2])
apply (simp add: constr_cinv_def op_prod_def \<epsilon>_left_id op_option_def del: \<epsilon>_dfset_def \<epsilon>_dset_def)
apply (simp add: upred_entails.rep_eq upred_valid.rep_eq upred_pure.rep_eq prod_n_valid_def \<epsilon>_n_valid del: \<epsilon>_dfset_def \<epsilon>_dset_def)
apply (simp add: valid_raw_option_def valid_frac[symmetric] split: option.splits)
by (metis dcamera_valid_iff less_eq_frac.rep_eq one_frac.rep_eq one_frac_def valid_raw_frac.rep_eq)

lemma cinv_own_1_l: "upred_holds (cinv_own 1 -\<^emph> cinv_own q -\<^emph> \<upharpoonleft>False)"
proof (rule upred_wand_holds2I)
  from one_op have "(1\<cdot>q \<le> 1) \<longleftrightarrow> False" by (simp add: less_le_not_le)
  with upred_wand_holds2E[OF cinv_own_valid, of 1 q] show "cinv_own 1 \<^emph> cinv_own q \<turnstile> \<upharpoonleft>False" by simp
qed
end