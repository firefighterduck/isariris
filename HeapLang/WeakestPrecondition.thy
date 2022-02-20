theory WeakestPrecondition
imports "../IrisCore/Invariant" "../IrisCore/AuthHeap" HeapLang State PrimitiveLaws Notation
begin

subsection \<open>Weakest Preconditions\<close>

definition state_interp :: "state \<Rightarrow> observation list \<Rightarrow> iprop" where
  "state_interp \<sigma> \<kappa>s = heap_interp (heap \<sigma>) \<^emph> proph_map_interp \<kappa>s (used_proph_id \<sigma>)"

datatype stuckness = NotStuck | MaybeStuck
instantiation stuckness :: ord begin
fun less_eq_stuckness :: "stuckness \<Rightarrow> stuckness \<Rightarrow> bool" where
  "less_eq_stuckness MaybeStuck NotStuck = False"
| "less_eq_stuckness _ _ = True"
fun less_stuckness :: "stuckness \<Rightarrow> stuckness \<Rightarrow> bool" where
  "less_stuckness MaybeStuck NotStuck = False"
| "less_stuckness MaybeStuck MaybeStuck = False"
| "less_stuckness NotStuck NotStuck = False"
| "less_stuckness _ _ = True"
instance ..
end

definition fill :: "ectx_item list \<Rightarrow> expr \<Rightarrow> expr"  where "fill K e =  fold fill_item K e"

definition prim_step :: "expr \<Rightarrow> state \<Rightarrow> observation list \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> bool" where
  "prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs \<equiv> \<exists>K e1' e2'. ((e1=fill K e1') \<and> (e2=fill K e2') \<and> head_step e1' \<sigma>1 \<kappa> e2' \<sigma>2 efs)"

function wp :: "stuckness \<Rightarrow> mask \<Rightarrow> expr \<Rightarrow> (val \<Rightarrow> iprop) \<Rightarrow> iprop" where
  "wp s E e1 \<Phi> = (case HeapLang.to_val e1 of Some v \<Rightarrow> \<Turnstile>{E}=> (\<Phi> v)
    | None \<Rightarrow> (\<forall>\<^sub>u \<sigma>1 \<kappa> \<kappa>s.
      ((state_interp \<sigma>1 (\<kappa>@\<kappa>s)) ={E,Set.empty}=\<^emph>
        ((\<upharpoonleft>(case s of NotStuck \<Rightarrow> red e1 \<sigma>1 | _ \<Rightarrow> True)) \<^emph>
        (\<forall>\<^sub>u e2 \<sigma>2 efs. ((\<upharpoonleft>(prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs))
          ={Set.empty}\<triangleright>=\<^emph> (\<Turnstile>{Set.empty,E}=> ((state_interp \<sigma>2 \<kappa>s) \<^emph>
            (wp s E e2 \<Phi>) \<^emph> ([\<^emph>\<^sub>l:] efs (\<lambda>ef. wp s UNIV ef (\<lambda>_. upred_emp)))))))))))"
by auto

abbreviation WP :: "expr \<Rightarrow> (val \<Rightarrow> iprop) \<Rightarrow> iprop" ("WP _ {{ _ }}") where
  "WP e {{ \<Phi> }} \<equiv> wp NotStuck {} e \<Phi>"

text \<open>
  First we show that all basic properties of wp hold for inputs in the domain, then we 
  always assume all values to lie in the domain.
\<close>
context begin
lemma wp_value_fupd: 
  assumes "wp_dom (s, E, Val v, P)"
  shows "wp s E (of_val v) P \<stileturn>\<turnstile> \<Turnstile>{E}=> P v"
  by (auto simp: wp.psimps[OF assms])

lemma wp_value: 
  assumes "wp_dom (s, E, Val v, P)"
  shows "P v \<turnstile> wp s E (Val v) P"
  by (auto simp: wp.psimps[OF assms] fupd_intro upred_wand_holdsE)

lemma wp_strong_mono: 
  assumes "wp_dom (s1, E1, e, P)" "wp_dom (s2, E2, e, Q)"
    "s1 \<le> s2" "E1 \<subseteq> E2" 
  shows "wp s1 E1 e P -\<^emph> (\<forall>\<^sub>u v. (P v ={E2}=\<^emph> Q v)) -\<^emph> wp s2 E2 e Q"
  apply (rule upred_wand_holds2I)
  sorry

lemma wp_lift_step_fupdN: 
assumes "HeapLang.to_val e1 = None"
shows "(\<forall>\<^sub>u \<sigma>1 \<kappa> \<kappa>s. ((state_interp \<sigma>1 (\<kappa>@\<kappa>s)) ={E,Set.empty}=\<^emph>
  ((\<upharpoonleft>(case s of NotStuck \<Rightarrow> red e1 \<sigma>1 | _ \<Rightarrow> True)) \<^emph>
  (\<forall>\<^sub>u e2 \<sigma>2 efs. ((\<upharpoonleft>(prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs)) ={Set.empty}\<triangleright>=\<^emph> 
    (\<Turnstile>{Set.empty,E}=> ((state_interp \<sigma>2 \<kappa>s) \<^emph>
      (wp s E e2 \<Phi>) \<^emph> ([\<^emph>\<^sub>l:] efs (\<lambda>ef. wp s UNIV ef (\<lambda>_. upred_emp))))))))))
   \<turnstile> wp s E e1 \<Phi>"
 sorry (* Axiomatized as reasoning with wp_dom is quite hard.*)
end   
end