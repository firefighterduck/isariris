theory Invariant
imports DerivedConstructions BaseLogicShallow Frac AuthHeap Misc
begin

subsection \<open> Namespaces \<close>
text \<open> 
  Namespaces in the stdpp library for Coq are quite sophisticated and require some features
  that Isabelle doesn't have. Thus, we use a less flexible but similar, easier version.
\<close>
type_synonym namespace = "nat list"
type_synonym name = "nat list"
definition names :: "namespace \<Rightarrow> name set" where
  "names N = {n. \<exists>p. n=N@p}" \<comment> \<open> A namespace is used as the prefix for other names. \<close>

definition subnamespace :: "namespace \<Rightarrow> namespace \<Rightarrow> bool" where
  "subnamespace N1 N2 \<equiv> \<exists>p. N1=N2@p"
lemma sub_names: "subnamespace N1 N2 \<longleftrightarrow> N1 \<in> names N2"
  by (auto simp: names_def subnamespace_def)  
lemma distinct_names: "\<lbrakk>\<not>subnamespace N1 N2; \<not>subnamespace N2 N1\<rbrakk> \<Longrightarrow> names N1 \<inter> names N2 = {}"
  by (auto simp: names_def subnamespace_def) (metis append_eq_append_conv2)
  
subsection \<open> Invariants \<close>
text \<open>The underlying invariant camera, contains the invariants and enabled/disabled names.\<close>
(* The Coq formalization uses positive integers instead of naturals. *)
codatatype invGS = Inv "(name\<rightharpoonup>invGS iprop later ag) auth" "name dset" "name dfset"

text \<open>The modular invariant camera based on the heap camera\<close>
type_synonym ('l,'v,'a,'c) invCmra = "('l,'v,'a invGS\<times>'c) heapCmra"
definition own_inv :: "'a::ucamera invGS \<Rightarrow> ('l,'v::ofe,'a,'c::ucamera) invCmra iprop" ("Own\<^sub>i _") where
  "own_inv i = Own(\<epsilon>,i,\<epsilon>)"

context assumes "SORT_CONSTRAINT('c::ucamera)" and "SORT_CONSTRAINT('v::ofe)"
begin

text \<open>Allocate new invariant map\<close>
definition ownI :: "name \<Rightarrow> 'a::ucamera iprop \<Rightarrow> ('l,'v,'a,'c) invCmra iprop" where
  "ownI \<iota> P = Own\<^sub>i (fragm [\<iota>\<mapsto>to_ag (Next P)],\<epsilon>,\<epsilon>)"

definition inv :: "namespace \<Rightarrow> 'a::ucamera iprop \<Rightarrow> ('l,'v,'a,'c) invCmra iprop" where
  "inv N P = \<exists>\<^sub>u \<iota>. ((\<upharpoonleft>(\<iota>\<in>names N)) \<and>\<^sub>u ownI \<iota> P)"
  
text \<open>Allocate new enabled invariant map\<close>
definition ownE :: "name dset \<Rightarrow> ('l,'v,'a::ucamera,'c) invCmra iprop" where
  "ownE E = Own\<^sub>i (\<epsilon>,E,\<epsilon>)"

text \<open>Allocate new disabled invariant map\<close>
definition ownD :: "name dfset \<Rightarrow> ('l,'v,'a::ucamera,'c) invCmra iprop" where
  "ownD D = Own\<^sub>i (\<epsilon>,\<epsilon>,D)"  
  
definition lift_inv_map :: "(name\<rightharpoonup>('a::ucamera) iprop) \<Rightarrow> (name\<rightharpoonup>'a iprop later ag)" where
  "lift_inv_map = (\<circ>) (map_option (to_ag \<circ> Next))"
  
text \<open>World satisfaction, i.e. the invariant that holds all invariants\<close>
(* Doesn't type check *)  
definition wsat :: "('l,'v,'a::ucamera,'c) invCmra iprop" where
  "wsat \<equiv> \<exists>\<^sub>u (I::name\<rightharpoonup>'a iprop).
    ((Own\<^sub>i(full(lift_inv_map I),\<epsilon>,\<epsilon>))
    \<^emph> (sep_map_set (\<lambda>\<iota>. ((\<triangleright>((the \<circ> I) \<iota>)) \<^emph> ownD (DFSet {|\<iota>|})) \<or>\<^sub>u (ownE (DSet {\<iota>}))) (dom I))
  )"
\<comment> \<open> The problem here:
  - Own\<^sub>i(full(lift_inv_map I),\<epsilon>,\<epsilon>) is of type ('l,'v,'a,'c) invCmra iprop, i.e. an iprop which 
    talks about has resources in the heap ('l\<rightharpoonup>'v), in invariants (based on 'a) and the camera 'c

  - \<triangleright>((the \<circ> I) \<iota> is of type 'a iprop, i.e. only talks about resources of camera 'a

  - 'a would need to be the same as ('l,'v,'a,'c) invCmra, which is a cyclic type definition and only
    possible if we find a fixed point type
\<close>
  
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