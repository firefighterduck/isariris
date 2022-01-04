theory WeakestPrecondition
imports "../IrisCore/BaseLogicShallow" "../IrisCore/AuthHeap" HeapLang State
begin

subsection \<open>Weakest Preconditions\<close>
context fixes red :: "expr \<Rightarrow> state \<Rightarrow> ('a::ucamera) iprop"
  and step :: "expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> 'a iprop"
begin
fun wp :: "expr \<Rightarrow> (val \<Rightarrow> 'a iprop) \<Rightarrow> 'a iprop" where
  "wp e \<Phi> = (case to_val e of Some v \<Rightarrow> \<Phi> v 
    | None \<Rightarrow> \<forall>\<^sub>u(\<lambda>\<sigma>. red e \<sigma> \<and>\<^sub>u \<triangleright>(\<forall>\<^sub>u(\<lambda>(e2,\<sigma>2). (step e \<sigma> e2 \<sigma>2 []) -\<^emph> wp e2 \<Phi>))))"
end