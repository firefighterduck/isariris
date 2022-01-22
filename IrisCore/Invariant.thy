theory Invariant
imports DerivedConstructions BaseLogicShallow Frac AuthHeap Misc "../SpanningTree/SpanningTreeCameras"
  Namespace iPropShallow 
begin

subsection \<open> Invariants \<close>

text \<open>The modular invariant camera based on the heap camera\<close>
definition own_inv :: "inv \<Rightarrow> iprop" ("Own\<^sub>i _") where
  "own_inv i = Own(\<epsilon>,\<epsilon>,i,\<epsilon>)"

context assumes "SORT_CONSTRAINT('c::ucamera)" and "SORT_CONSTRAINT('v::ofe)"
begin

text \<open>Allocate new invariant map\<close>
definition ownI :: "name \<Rightarrow> iprop \<Rightarrow> iprop" where
  "ownI \<iota> P = Own\<^sub>i (fragm [\<iota>\<mapsto>to_ag (Next (pre P))],\<epsilon>,\<epsilon>)"

definition inv :: "namespace \<Rightarrow> iprop \<Rightarrow>  iprop" where
  "inv N P = \<exists>\<^sub>u \<iota>. ((\<upharpoonleft>(\<iota>\<in>names N)) \<and>\<^sub>u ownI \<iota> P)"
  
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
  (auto simp add: prod_pcore_id_pred \<epsilon>_pcore_id_def fragm_core_id simp del: \<epsilon>_dfset_def \<epsilon>_dset_def)

lemma "persistent (inv N P)"
  unfolding inv_def
  apply (rule persistent_exists)
  apply (rule allI)
  apply (rule persistent_conj)
  apply (rule persistent_pure)
  by (rule persistent_ownI)
end