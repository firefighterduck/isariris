theory SpanningTreeCameras
imports Graph
  "../IrisCore/Frac"
  "../HeapLang/HeapLang"
  "../HeapLang/PrimitiveLaws"
  "../IrisCore/BaseLogicShallow"
begin

(* Children locations, in Coq it's a leibniz0 structure*)
type_synonym chl = "loc option\<times>loc option"

(* The graph camera, a unital camera. *)
type_synonym graphUR = "((loc\<rightharpoonup>(chl ex))\<times>frac) option"

(* A camera for duplicatable markings *)
type_synonym markingUR = "loc set"

(* 
  This would normally be a list of camera functors to allow for modular reasoning.
  Isabelle does not support type lists and thus we use a tuple for this simple example.  
*)
type_synonym graphG = "graphUR auth \<times> markingUR auth \<times> heapGS"

abbreviation own_graph :: "graphUR auth \<Rightarrow> graphG iprop" ("Own\<^sub>g _") where
  "own_graph \<equiv> \<lambda>g. Own(g, \<epsilon>)"
abbreviation own_marking :: "markingUR auth \<Rightarrow> graphG iprop" ("Own\<^sub>m _") where
  "own_marking \<equiv> \<lambda>m. Own(\<epsilon>, m, \<epsilon>)"
abbreviation own_heap :: "heapGS \<Rightarrow> graphG iprop" ("Own\<^sub>h _") where
  "own_heap \<equiv> \<lambda>h. Own(\<epsilon>, \<epsilon>, h)"

definition points_to_graph :: "loc \<Rightarrow> dfrac \<Rightarrow> val \<Rightarrow> graphG iprop" where
  "points_to_graph l dq v = Own\<^sub>h(Heap [l\<mapsto>(dq, to_ag (Some v))])"
abbreviation points_to_disc :: "loc \<Rightarrow> val \<Rightarrow> graphG iprop" where 
  "points_to_disc \<equiv> \<lambda>l v. points_to_graph l DfracDiscarded v"
abbreviation points_to_own :: "loc \<Rightarrow> frac \<Rightarrow> val \<Rightarrow> graphG iprop" where
  "points_to_own \<equiv> \<lambda>l p v. points_to_graph l (DfracOwn p) v"
abbreviation points_to_full :: "loc \<Rightarrow> val \<Rightarrow> graphG iprop" where
  "points_to_full \<equiv> \<lambda>l v. points_to_own l 1 v"

bundle graphG_syntax begin
  notation points_to_graph ("_ \<mapsto>{_} _" 60)
  notation points_to_disc (infix "\<mapsto>\<box>" 60)
  notation points_to_own ("_\<mapsto>{#_}_" 60)
  notation points_to_full (infix "\<mapsto>\<^sub>u" 60)
end

context includes graphG_syntax begin
lemma graphG_points_to_valid: "upred_holds ((l \<mapsto>{dq} v) -\<^emph> \<upharpoonleft>(valid dq))"
proof -
  have "(l \<mapsto>{dq} v) \<turnstile> \<V>((\<epsilon>, \<epsilon>, Heap [l\<mapsto>(dq,to_ag (Some v))])::graphG)" 
      by (auto simp: points_to_graph_def own_valid)
  moreover have "\<V>((\<epsilon>, \<epsilon>, Heap [l\<mapsto>(dq,to_ag (Some v))])::graphG) 
    \<turnstile> \<upharpoonleft>(valid((\<epsilon>, \<epsilon>, Heap [l\<mapsto>(dq,to_ag (Some v))])::graphG))"
    using discrete_valid upred_entail_eq_def by auto
  moreover have "valid((\<epsilon>, \<epsilon>, Heap [l\<mapsto>(dq,to_ag (Some v))])::graphG) 
    \<longleftrightarrow> valid(Heap [l\<mapsto>(dq,to_ag (Some v))])"
    by (auto simp: prod_valid_def \<epsilon>_valid)
  ultimately have "(l \<mapsto>{dq} v) \<turnstile> \<upharpoonleft>(valid dq)" 
    by (auto simp: frag_heap_valid intro: upred_entails_trans)
  from upred_wand_holdsI [OF this] show ?thesis .
qed

lemma graphG_points_to_agree: 
  "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> (l \<mapsto>{dq2} v2) -\<^emph> \<upharpoonleft>(v1 = v2))"
proof -
  have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> (l \<mapsto>{dq2} v2) -\<^emph> 
    \<V>((\<epsilon>,\<epsilon>,Heap [l\<mapsto>(dq1, to_ag (Some v1))])\<cdot>(\<epsilon>,\<epsilon>,Heap [l\<mapsto>(dq2, to_ag (Some v2))])::graphG))"
    apply (auto simp: points_to_graph_def) using own_valid2 by auto
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> (l \<mapsto>{dq2} v2) -\<^emph> 
    \<V>((\<epsilon>,\<epsilon>,Heap ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))]))::graphG))" 
    by (auto simp: op_prod_def \<epsilon>_left_id heap_op)
  from upred_entails_wand_holdsR2[OF upred_entail_eqL[OF discrete_valid] this] 
  have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> (l \<mapsto>{dq2} v2) -\<^emph> 
    \<upharpoonleft>(All (heap_rel [l\<mapsto>(dq1\<cdot>dq2, to_ag (Some v1)\<cdot>to_ag (Some v2))])))" 
    by (auto simp: valid_raw_heap.rep_eq valid_def op_prod_def valid_raw_prod_def sprop_conj.rep_eq \<epsilon>_n_valid)
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> (l \<mapsto>{dq2} v2) -\<^emph> 
    \<upharpoonleft>(valid (dq1\<cdot>dq2) \<and> (\<forall>n. \<exists>ag. n_equiv n (to_ag (Some v1)\<cdot>to_ag (Some v2)) (to_ag ag))))"
    by (smt (z3) fun_upd_same pure_entailsI upred_entails_wand_holdsR2)
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> (l \<mapsto>{dq2} v2) -\<^emph>
    \<upharpoonleft>(\<forall>n. \<exists>ag. n_equiv n (to_ag (Some v1)\<cdot>to_ag (Some v2)) (to_ag ag)))"
    using upred_entails_wand_holdsR2 pure_entailsI by (metis (no_types, lifting))
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> (l \<mapsto>{dq2} v2) -\<^emph> 
    \<upharpoonleft>(\<exists>ag. to_ag (Some v1)\<cdot>to_ag (Some v2) = to_ag ag))" using d_equiv by (smt (verit, ccfv_SIG))
  then show ?thesis 
    by (smt (z3) option.inject pure_entailsI singleton_inject to_ag.rep_eq to_ag_op upred_entails_wand_holdsR2)
qed

lemma graphG_points_to_combine: 
  "upred_holds ((l\<mapsto>{dq1} v1) -\<^emph> (l\<mapsto>{dq2} v2) -\<^emph> (l\<mapsto>{dq1\<cdot>dq2} v1) \<^emph> \<upharpoonleft>(v1=v2))"
  apply (rule upred_wand_holds2I)
  apply (rule upred_sep_pure)
  apply (rule entails_pure_extend[OF upred_wandE[OF upred_wand_holdsE[OF graphG_points_to_agree]]])
  apply (unfold points_to_graph_def)[1]
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF own_op]])
  apply (simp add: op_prod_def \<epsilon>_left_id heap_op_val_eq)
  by (rule upred_wandE[OF upred_wand_holdsE[OF graphG_points_to_agree]])

lemma graphG_points_to_frac_ne: 
  assumes "\<not> (valid (dq1\<cdot>dq2))"
  shows "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> (l2 \<mapsto>{dq2} v2) -\<^emph> \<upharpoonleft>(l1\<noteq>l2))"
proof -
  from upred_wand_holds2I[OF upred_entails_trans[OF upred_wand_holds2E[OF own_valid2] 
    upred_entail_eqL[OF discrete_valid]]]
  have "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> (l2 \<mapsto>{dq2} v2) -\<^emph>
    \<upharpoonleft>(valid ((\<epsilon>,\<epsilon>,Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (\<epsilon>,\<epsilon>,Heap [l2\<mapsto>(dq2,to_ag (Some v2))])::graphG)))"
    by (auto simp: points_to_graph_def)
  then have base: "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> (l2 \<mapsto>{dq2} v2) -\<^emph>
    \<upharpoonleft>(valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))]))))"
    by (auto simp: op_prod_def \<epsilon>_left_id prod_valid_def \<epsilon>_valid)
  from assms have "\<not> (\<forall>n. heap_rel ([l1\<mapsto>(dq1,to_ag (Some v1))\<cdot>(dq2,to_ag (Some v2))]) n)"
    by (auto simp: op_fun_def valid_def op_prod_def)
  with heap_valid_op have "valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))])) =
    (l1\<noteq>l2 \<and> valid (Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<and> valid (Heap [l2\<mapsto>(dq2,to_ag (Some v2))]))"
    by metis
  then have "\<upharpoonleft>(valid ((Heap [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (Heap [l2\<mapsto>(dq2,to_ag (Some v2))]))) \<turnstile>
    \<upharpoonleft>(l1\<noteq>l2)" using pure_entailsI by blast
  from upred_entails_wand_holdsR2[OF this base] show ?thesis .
qed

lemma graphG_points_to_ne: "upred_holds ((l1\<mapsto>\<^sub>uv1) -\<^emph> (l2\<mapsto>{dq2} v2) -\<^emph> \<upharpoonleft>(l1\<noteq>l2))"
  by (rule graphG_points_to_frac_ne[OF dfrac_not_valid_own])
end
end