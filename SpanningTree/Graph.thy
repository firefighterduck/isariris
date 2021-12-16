theory Graph
imports Main
begin

section \<open> Spanning Tree example\<close>
text \<open> A simple example application of the Iris base logic;
  based on https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/spanning_tree/graph.v\<close>

subsection \<open> Graph definition \<close>

type_synonym 'a graph = "'a \<rightharpoonup> ('a option\<times>'a option)"

definition get_left :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "get_left g x = Option.bind (g x) fst"
definition get_right :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "get_right g x = Option.bind (g x) snd"

fun strict_sub_child :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "strict_sub_child (Some c) (Some c') = (c=c')"
| "strict_sub_child (Some _) None = True"
| "strict_sub_child None (Some _) = False"
| "strict_sub_child None None = True"

definition strict_sub_children :: "'a option\<times>'a option \<Rightarrow> 'a option\<times>'a option \<Rightarrow> bool" where
  "strict_sub_children ch ch' 
    \<equiv> strict_sub_child (fst ch) (fst ch') \<and> strict_sub_child (snd ch) (snd ch')"

definition strict_subgraph :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> bool" where
  "strict_subgraph g1 g2 \<equiv> 
    \<forall>x. strict_sub_children (get_left g1 x, get_right g1 x) (get_left g2 x, get_right g2 x)"

(* Path defined by whether a step went left (True) or right (False). Empty path stays at the node. *)
type_synonym path = "bool list"

inductive valid_path :: "'a graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> path \<Rightarrow> bool" where
  valid_pathE: "\<lbrakk>x\<in>dom g; x=y\<rbrakk> \<Longrightarrow> valid_path g x y []"
| valid_pathL: "\<lbrakk>get_left g x = Some xl; valid_path g xl y p\<rbrakk> \<Longrightarrow> valid_path g x y (True#p)"
| valid_pathR: "\<lbrakk>get_right g x = Some xr; valid_path g xr y p\<rbrakk> \<Longrightarrow> valid_path g x y (False#p)"

definition connected :: "'a graph \<Rightarrow> 'a \<Rightarrow> bool" where
  "connected g x \<equiv> \<forall>z\<in>dom g. \<exists>p. valid_path g x z p"

definition front :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "front g t1 t2 \<equiv> t1\<subseteq>dom g \<and> (\<forall>x\<in>t1. \<forall>v. ((get_left g x = Some v) \<or> (get_right g x = Some v)) \<longrightarrow> v\<in>t2)"

definition maximal :: "'a graph \<Rightarrow> bool" where "maximal g \<equiv> front g (dom g) (dom g)"

definition tree :: "'a graph \<Rightarrow> 'a \<Rightarrow> bool" where
  "tree g x \<equiv> \<forall>z\<in>dom g. (\<exists>p. valid_path g x z p \<and> (\<forall>p'. valid_path g x z p' \<longrightarrow> (p=p')))"

(* Lemmas omitted for now, will only add as axioms when needed. *)
end