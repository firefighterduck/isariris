theory WeakestPrecondition
imports "../IrisCore/Invariant" "../IrisCore/AuthHeap" HeapLang State PrimitiveLaws
begin

subsection \<open>Weakest Preconditions\<close>

definition state_interp :: "state \<Rightarrow> observation list \<Rightarrow> iprop" where
  "state_interp \<sigma> \<kappa>s = heap_interp (heap \<sigma>) \<^emph> proph_map_interp \<kappa>s (used_proph_id \<sigma>)"

datatype stuckness = NotStuck | MaybeStuck

definition fill :: "ectx_item list \<Rightarrow> expr \<Rightarrow> expr"  where "fill K e =  fold fill_item K e"

inductive prim_step :: "expr \<Rightarrow> state \<Rightarrow> observation list \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> bool" where
Ectx_step:  "\<lbrakk>e1=fill K e1'; e2=fill K e2'; head_step e1' \<sigma>1 \<kappa> e2' \<sigma>2 efs\<rbrakk> \<Longrightarrow>
   prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs"

function wp :: "stuckness \<Rightarrow> mask \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> iprop) \<Rightarrow> iprop" where
  "wp s E e1 \<Phi> = (case to_val e1 of Some v \<Rightarrow> (\<Turnstile>{E}=> (\<Phi> v))
    | None \<Rightarrow> (\<forall>\<^sub>u \<sigma>1 \<kappa> \<kappa>s.
      ((state_interp \<sigma>1 (\<kappa>@\<kappa>s)) ={E,Set.empty}=\<^emph>
        ((\<upharpoonleft>(case s of NotStuck \<Rightarrow> red e1 \<sigma>1 | _ \<Rightarrow> True)) \<^emph>
        (\<forall>\<^sub>u e2 \<sigma>2 efs. ((\<upharpoonleft>(prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs))
          ={Set.empty}\<triangleright>=\<^emph> (\<Turnstile>{Set.empty,E}=> ((state_interp \<sigma>2 \<kappa>s) \<^emph>
            (wp s E e2 \<Phi>) \<^emph> ([\<^emph>\<^sub>l:] efs (\<lambda>ef. wp s UNIV ef (\<lambda>_. upred_emp)))))))))))"
by auto            

end