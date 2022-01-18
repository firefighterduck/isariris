theory Misc
imports BaseLogicShallow
begin

definition map_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<times>'v\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "map_heap h f a = folding_on.F f a {(l,v) |l v. h l = Some v}"

definition sep_map_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<times>'v\<Rightarrow>('a::ucamera) iprop) \<Rightarrow> 'a iprop" where
  "sep_map_heap h f = map_heap h (\<lambda>lv a. a \<^emph> f lv) (\<upharpoonleft>True)"

definition sep_map_set :: "('b\<Rightarrow>('a::ucamera) iprop) \<Rightarrow> 'b set \<Rightarrow> 'a iprop" where
  "sep_map_set f s = folding_on.F (\<lambda>x a. a \<^emph> f x) (\<upharpoonleft>True) s"

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
end