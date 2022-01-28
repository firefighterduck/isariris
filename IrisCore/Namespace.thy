theory Namespace
imports Main
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

definition nroot :: namespace where "nroot = []"
definition add_name :: "namespace \<Rightarrow> name \<Rightarrow> namespace" where "add_name N n = N@n"
definition string_to_name :: "string \<Rightarrow> name" where 
  "string_to_name = (map nat_of_integer) \<circ> String.asciis_of_literal \<circ> String.implode"

definition subnamespace :: "namespace \<Rightarrow> namespace \<Rightarrow> bool" where
  "subnamespace N1 N2 \<equiv> \<exists>p. N1=N2@p"
lemma sub_names: "subnamespace N1 N2 \<longleftrightarrow> N1 \<in> names N2"
  by (auto simp: names_def subnamespace_def)  
lemma distinct_names: "\<lbrakk>\<not>subnamespace N1 N2; \<not>subnamespace N2 N1\<rbrakk> \<Longrightarrow> names N1 \<inter> names N2 = {}"
  by (auto simp: names_def subnamespace_def) (metis append_eq_append_conv2)
end