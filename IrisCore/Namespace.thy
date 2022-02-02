theory Namespace
imports BasicTypes
begin
subsection \<open> Namespaces \<close>
text \<open> 
  Namespaces in the stdpp library for Coq are quite sophisticated and require some features
  that Isabelle doesn't have. Thus, we use a less flexible but similar, easier version.
\<close>
type_synonym namespace = "nat list"
type_synonym name = "nat list"
definition names :: "namespace \<Rightarrow> name set" where
  "names N = {n. \<exists>p. n=p@N}" \<comment> \<open> A namespace is used as the prefix for other names. \<close> 
definition dnames :: "namespace \<Rightarrow> name dset" where "dnames N = DSet (names N)"

definition nroot :: namespace where "nroot = []"
definition add_name :: "namespace \<Rightarrow> name \<Rightarrow> namespace" where "add_name N n = n@N"

lemma add_name_names: "add_name N n \<in> names N"
  unfolding names_def add_name_def
  apply (induction N arbitrary: n)
  by auto

lemma add_name_subseq_names: "names (add_name N n) \<subseteq> names N"
  unfolding names_def add_name_def
  apply (induction N arbitrary: n)
  by auto

lemma cons_subseq_names: "names (a#N) \<subseteq> names N"
  using add_name_subseq_names[of _ "[a]"] unfolding add_name_def by simp

lemma add_name_minus: "names (add_name N n) = names N - {n'. (\<exists>p. n'=p@N) \<and> (\<nexists>q. n'=q@n@N)}"
  unfolding names_def add_name_def
  by auto

lemma add_name_subs_names: "n\<noteq>[] \<Longrightarrow> names (add_name N n) \<subset> names N"
  using add_name_minus names_def by fastforce

lemma union_add_names: "\<Union> {names (add_name N n) | n. True} = names N"
unfolding names_def add_name_def by auto

lemma infinite_names: "infinite (names N)"
proof
  assume assm: "finite (names N)"
  have "{x#N | x. True} \<subseteq> names N"
    unfolding names_def by auto
  from rev_finite_subset[OF assm this] have "finite {x#N | x. True}" .
  then have "finite ((\<lambda>x. x#N) ` UNIV)" by (simp add: full_SetCompr_eq)
  have "inj_on (\<lambda>x. x#N) UNIV" by (meson injI list.inject)
  from  finite_imageD[OF \<open>finite ((\<lambda>x. x#N) ` UNIV)\<close> this] have "finite (UNIV::nat set)" .
  with infinite_UNIV_nat show False ..
qed 

lemma not_no_names: "names N \<noteq> {}" by (simp add: infinite_imp_nonempty infinite_names)

definition string_to_name :: "string \<Rightarrow> name" where 
  "string_to_name = (map nat_of_integer) \<circ> String.asciis_of_literal \<circ> String.implode"

definition subnamespace :: "namespace \<Rightarrow> namespace \<Rightarrow> bool" where
  "subnamespace N1 N2 \<equiv> \<exists>p. N1=p@N2"
lemma sub_names: "subnamespace N1 N2 \<longleftrightarrow> N1 \<in> names N2"
  by (auto simp: names_def subnamespace_def)  
lemma distinct_names: "\<lbrakk>\<not>subnamespace N1 N2; \<not>subnamespace N2 N1\<rbrakk> \<Longrightarrow> names N1 \<inter> names N2 = {}"
  by (auto simp: names_def subnamespace_def) (metis append_eq_append_conv2)
end