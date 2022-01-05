theory WeakestPrecondition
imports "../IrisCore/BaseLogicShallow" "../IrisCore/AuthHeap" HeapLang State PrimitiveLaws
begin

subsection \<open>Weakest Preconditions\<close>
text \<open>
  The functions below mirror the stepwise derivation of wp from "Iris from ground up".
  wp2 and wp3 differ to the paper description in that they take a \<Phi> which does not return iprop 
  but only the underlying camera. This needs to be changed lateron but helps typechecking for now.
\<close>
function wp1 :: "expr \<Rightarrow> (val \<Rightarrow> ('a::ucamera) iprop) \<Rightarrow> 'a iprop" where
  "wp1 e \<Phi> = (case to_val e of Some v \<Rightarrow> \<Phi> v 
    | None \<Rightarrow> \<forall>\<^sub>u(\<lambda>\<sigma>. (\<upharpoonleft>(red e \<sigma>)) \<and>\<^sub>u \<triangleright>(\<forall>\<^sub>u(\<lambda>(\<kappa>,e2,\<sigma>2). (\<upharpoonleft>(e \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 [])) -\<^emph> wp1 e2 \<Phi>))))"
    by fastforce blast

definition own_state_heap :: "state \<Rightarrow> (loc,val option,'c::ucamera) heapCmra iprop" where
  "own_state_heap s = Own\<^sub>h (full (to_heap_op (heap s)))"

function wp2 :: "expr \<Rightarrow> (val \<Rightarrow> 'a::ucamera) \<Rightarrow> (loc,val option,'a) heapCmra iprop" where
  "wp2 e \<Phi> = (case to_val e of Some v \<Rightarrow> \<Rrightarrow>\<^sub>b (own_other (\<Phi> v))
    | None \<Rightarrow> \<forall>\<^sub>u(\<lambda>\<sigma>. own_state_heap \<sigma> -\<^emph>
      \<Rrightarrow>\<^sub>b ((\<upharpoonleft>(red e \<sigma>)) \<and>\<^sub>u \<triangleright>(\<forall>\<^sub>u(\<lambda>(\<kappa>,e2,\<sigma>2). (\<upharpoonleft>(e \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 [])) -\<^emph> 
        \<Rrightarrow>\<^sub>b ((own_state_heap \<sigma>2) \<^emph> wp2 e2 \<Phi>))))))"
   by fast simp

function wp3 :: "expr \<Rightarrow> (val \<Rightarrow> 'a::ucamera) \<Rightarrow> (loc,val option,'a) heapCmra iprop" where
  "wp3 e \<Phi> = (case to_val e of Some v \<Rightarrow> \<Rrightarrow>\<^sub>b (own_other (\<Phi> v))
    | None \<Rightarrow> \<forall>\<^sub>u(\<lambda>\<sigma>. own_state_heap \<sigma> -\<^emph>
      \<Rrightarrow>\<^sub>b ((\<upharpoonleft>(red e \<sigma>)) \<and>\<^sub>u \<triangleright>(\<forall>\<^sub>u(\<lambda>(\<kappa>,e2,\<sigma>2,efs). (\<upharpoonleft>(e \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs)) -\<^emph> 
        \<Rrightarrow>\<^sub>b ((own_state_heap \<sigma>2) \<^emph> wp3 e2 \<Phi> \<^emph> (sep_map_set (\<lambda>e'. wp3 e' (\<lambda>_. \<epsilon>)) (set efs))))))))"
  by fast auto

abbreviation wp :: "expr \<Rightarrow> (val \<Rightarrow> 'a::ucamera) \<Rightarrow> (loc,val option,'a) heapCmra iprop" where 
  "wp \<equiv> wp3"
end