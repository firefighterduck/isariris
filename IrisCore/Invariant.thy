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
  "ownI \<iota> P = Own\<^sub>i (map_view_frag \<iota> DfracDiscarded (Next (pre P)),\<epsilon>,\<epsilon>)"

definition inv :: "namespace \<Rightarrow> iprop \<Rightarrow>  iprop" where
  "inv N P \<equiv> \<exists>\<^sub>u \<iota>. ((\<upharpoonleft>(\<iota>\<in>names N)) \<and>\<^sub>u ownI \<iota> P)"
  
text \<open>Allocate new enabled invariant map\<close>
definition ownE :: "name dset \<Rightarrow> iprop" where
  "ownE E = Own\<^sub>i (\<epsilon>,E,\<epsilon>)"

text \<open>Allocate new disabled invariant map\<close>
definition ownD :: "name dfset \<Rightarrow> iprop" where
  "ownD D = Own\<^sub>i (\<epsilon>,\<epsilon>,D)"  
  
definition lift_inv_fmap :: "(name,iprop) fmap \<Rightarrow> (name,pre_iprop later) fmap" where
  "lift_inv_fmap m = Abs_fmap (map_option (Next \<circ> pre) \<circ> (fmlookup m))"

lemma lift_inf_fmap_finite: "(map_option (Next \<circ> pre) \<circ> (fmlookup m)) \<in> {m. finite (dom m)}"
  by auto

text \<open>World satisfaction, i.e. the invariant that holds all invariants\<close>
definition wsat :: iprop where
  "wsat \<equiv> \<exists>\<^sub>u (I::(name,iprop) fmap).
    ((Own\<^sub>i(map_view_auth (DfracOwn 1) (lift_inv_fmap I),\<epsilon>,\<epsilon>))
    \<^emph> (sep_map_fmdom (\<lambda>\<iota>. ((\<triangleright>(the (fmlookup I \<iota>))) \<^emph> ownD (DFSet {|\<iota>|})) \<or>\<^sub>u (ownE (DSet {\<iota>}))) I)
  )"
end

lemma pcore_id_inv: "pcore_id_pred (constr_inv (map_view_frag \<iota> DfracDiscarded (Next (pre P)), \<epsilon>, \<epsilon>))"
  unfolding constr_inv_def prod_pcore_id_pred
  apply (simp add: \<epsilon>_pcore_id_def del: \<epsilon>_option_def \<epsilon>_dfset_def \<epsilon>_dset_def)
  by (rule pcore_id_frag[OF discarded_core_id])

lemma persistent_ownI: "persistent (ownI \<iota> P)"
  unfolding ownI_def own_inv_def by (rule persistent_core_own2[OF pcore_id_inv])

lemma persistent_inv: "persistent (inv N P)"
  unfolding inv_def
  apply (rule persistent_exists)
  apply (rule allI)
  apply (rule persistent_conj)
  apply (rule persistent_pure)
  by (rule persistent_ownI)

lemma auth_map_both_validI: 
  "\<V>(constr_inv (map_view_auth (DfracOwn 1) m,\<epsilon>,\<epsilon>) \<cdot> constr_inv (map_view_frag k dq v,\<epsilon>,\<epsilon>)) \<turnstile>
    (fmlookup m k =\<^sub>u Some v) \<and>\<^sub>u \<upharpoonleft>(valid dq)"
unfolding constr_inv_def op_prod_def
apply (simp add: \<epsilon>_left_id auth_comb_opL del: \<epsilon>_dfset_def \<epsilon>_dset_def \<epsilon>_option_def split: prod.splits)
apply (simp add: op_fun_def op_option_def del: \<epsilon>_dfset_def \<epsilon>_dset_def)
apply transfer
apply (simp add: prod_n_valid_def \<epsilon>_n_valid valid_raw_option_def del: \<epsilon>_dfset_def \<epsilon>_dset_def)
using map_view_both_valid by fastforce

lemma invariant_lookup: 
  "Own\<^sub>i (map_view_auth (DfracOwn 1) (lift_inv_fmap I),\<epsilon>,\<epsilon>) \<^emph> ownI \<iota> P \<turnstile> 
  (\<exists>\<^sub>u Q. \<upharpoonleft>(fmlookup I \<iota> = Some Q) \<^emph> \<triangleright>(Q=\<^sub>uP))"
  unfolding ownI_def own_inv_def
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF own_op]])
  apply (rule upred_entails_trans[OF own_valid])
  apply (rule upred_entails_trans[OF auth_map_both_validI])
  apply transfer'
  apply (auto simp: lift_inv_fmap_def valid_raw_dfrac_def valid_def n_equiv_option_def 
    n_equiv_later_def Abs_fmap_inverse[OF lift_inf_fmap_finite])
  apply (metis dual_order.refl n_incl_def ofe_refl prod_cases3 total_n_inclI)
  by (metis \<epsilon>_left_id ofe_refl prod_cases3) 
  
lemma "wsat \<^emph> ownI i P \<^emph> ownE (DSet {i}) \<turnstile> wsat \<^emph> (\<triangleright>P) \<^emph> ownD (DFSet {|i|})"
unfolding wsat_def
apply (rule pull_exists_antecedent2)
apply (rule upred_existsE')
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF upred_sep_assoc])
apply (rule upred_entails_trans[OF upred_sep_assoc'])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_assoc_rev])
apply (rule upred_entails_exchange[OF invariant_lookup])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule pull_exists_antecedent)
apply (rule upred_existsE')
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF upred_sep_assoc])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_pure_impl)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (simp add: sep_map_dom_delete del: \<epsilon>_dfset_def \<epsilon>_dset_def)
apply (rule upred_entails_trans[OF upred_sep_comm2R])
sorry

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
apply (simp add: upred_entails.rep_eq upred_valid.rep_eq upred_pure.rep_eq prod_n_valid_def \<epsilon>_n_valid 
  del: \<epsilon>_dfset_def \<epsilon>_dset_def)
apply (simp add: valid_raw_option_def valid_frac[symmetric] split: option.splits)
by (metis dcamera_valid_iff less_eq_frac.rep_eq one_frac.rep_eq one_frac_def valid_raw_frac.rep_eq)

lemma cinv_own_1_l: "upred_holds (cinv_own 1 -\<^emph> cinv_own q -\<^emph> \<upharpoonleft>False)"
proof (rule upred_wand_holds2I)
  from one_op have "(1\<cdot>q \<le> 1) \<longleftrightarrow> False" by (simp add: less_le_not_le)
  with upred_wand_holds2E[OF cinv_own_valid, of 1 q] show "cinv_own 1 \<^emph> cinv_own q \<turnstile> \<upharpoonleft>False" by simp
qed
end