theory AuthHeap
imports DerivedConstructions Frac BaseLogicShallow Misc
begin

subsubsection \<open>Auth based fragm\<close>
type_synonym ('l,'v) heap = "('l\<rightharpoonup>(dfrac\<times>'v ag)) auth"

lemma heap_auth_agree:
  "\<lbrakk>(f::'l\<rightharpoonup>(dfrac\<times>'v::discrete ag)) l = Some (d,v); valid (comb a f)\<rbrakk> \<Longrightarrow> \<exists>d'. a l = Some (d',v)"
proof -
  assume assms: "f l = Some (d,v)" "valid (comb a f)"
  then have "\<forall>n. n_incl n f a" by (auto simp: valid_def)
  then obtain f' where f': "a = (f\<cdot>f')" by (auto simp: n_incl_incl incl_def)
  then show ?thesis proof (cases "f' l")
    case None
    then have "(f\<cdot>f') l = f l " by (auto simp: op_fun_def op_option_def assms(1)) 
    with f' have "a l = f l" by (auto simp: incl_def)
    with assms(1) show ?thesis by simp
  next
    case (Some x)
    with f' have al: "a l = (f l) \<cdot> Some x" by (auto simp: op_fun_def)
    with f' Some assms(2) have al_valid: "valid ((f l) \<cdot> Some x)" 
      by (auto simp: valid_def op_fun_def) (metis valid_raw_fun.rep_eq)
    from f' assms(2) have "valid f'" apply (auto simp: valid_def) 
      by (metis camera_comm camera_valid_op)
    with Some obtain d' v' where x: "x = (d', v')" "valid v'" 
      by (auto simp: valid_def valid_raw_fun.rep_eq valid_raw_option_def valid_raw_prod_def 
        sprop_conj.rep_eq split: option.splits) (metis surj_pair)
    with al_valid assms(1) have "valid (v\<cdot>v')" 
      by (auto simp: valid_def valid_raw_option_def op_option_def op_prod_def prod_n_valid_def 
        split: option.splits)
    from d_ag_agree[OF this] al assms(1) x have "a l = Some (d\<cdot>d',v)" 
      by (auto simp: op_ag_def Rep_ag_inverse op_option_def op_prod_def)
    then show ?thesis ..
  qed
qed

lemma frag_heap_valid: "valid (fragm [k\<mapsto>(dq,to_ag v)]) \<longleftrightarrow> valid dq"
  by (auto simp: valid_def valid_raw_fun.rep_eq valid_raw_option_def prod_n_valid_def 
    to_ag_valid[unfolded valid_def])

lemma heap_op: "[l\<mapsto>(dq1, to_ag v1)]\<cdot>[l\<mapsto>(dq2, to_ag v2)] = [l\<mapsto>(dq1, to_ag v1)\<cdot>(dq2, to_ag v2)]"
  by (auto simp: op_fun_def op_option_def)

lemma heap_op_val_eq: "[l\<mapsto>(dq1, to_ag v)]\<cdot>[l\<mapsto>(dq2, to_ag v)] = [l\<mapsto>(dq1\<cdot>dq2, to_ag v)]" 
  unfolding heap_op by (auto simp: op_prod_def op_ag_def to_ag_def Rep_ag_inverse)
  
text \<open>The modular Heap camera\<close>
type_synonym ('l,'v,'c) heapCmra = "('l,'v) heap\<times>'c"
abbreviation own_heap :: "('l,'v::ofe) heap \<Rightarrow> ('l,'v,'c::ucamera) heapCmra iprop" ("Own\<^sub>h _") where
   "own_heap \<equiv> \<lambda>h. Own(h,\<epsilon>)"

abbreviation own_other :: "'c::ucamera \<Rightarrow> ('l,'v::ofe,'c::ucamera) heapCmra iprop" where
  "own_other \<equiv> \<lambda>c. Own(\<epsilon>,c)"
   
definition points_to :: "'l \<Rightarrow> dfrac \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option,'c::ucamera) heapCmra iprop" where
  "points_to l dq v = Own\<^sub>h(fragm [l\<mapsto>(dq, to_ag (Some v))])"
abbreviation points_to_disc :: "'l \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option,'c::ucamera) heapCmra iprop" where 
  "points_to_disc \<equiv> \<lambda>l v. points_to l DfracDiscarded v"
abbreviation points_to_own :: "'l \<Rightarrow> frac \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option,'c::ucamera) heapCmra iprop" where
  "points_to_own \<equiv> \<lambda>l p v. points_to l (DfracOwn p) v"
abbreviation points_to_full :: "'l \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option,'c::ucamera) heapCmra iprop" where
  "points_to_full \<equiv> \<lambda>l v. points_to_own l 1 v"

bundle points_to_syntax begin
  notation points_to ("_ \<mapsto>{_} _" 60)
  notation points_to_disc (infix "\<mapsto>\<box>" 60)
  notation points_to_own ("_\<mapsto>{#_}_" 60)
  notation points_to_full (infix "\<mapsto>\<^sub>u" 60)
end

context includes points_to_syntax assumes "SORT_CONSTRAINT('c::ucamera)" begin 

lemma points_to_valid: 
  "upred_holds (((l \<mapsto>{dq} v)::('a,'v::discrete option,'c) heapCmra iprop) -\<^emph> \<upharpoonleft>(valid dq))"
proof -
  have "((l \<mapsto>{dq} v)::('a,'v option,'c) heapCmra iprop) 
    \<turnstile> \<V>(fragm [l\<mapsto>(dq,to_ag (Some v))],\<epsilon>::'c)" by (auto simp: points_to_def own_valid)
  moreover have "\<V>(fragm [l\<mapsto>(dq,to_ag (Some v))],\<epsilon>::'c)\<turnstile>\<V>(fragm [l\<mapsto>(dq,to_ag (Some v))])"
     by (auto simp: upred_valid_def valid_def valid_raw_prod_def sprop_conj.rep_eq \<epsilon>_n_valid valid_raw_auth_def)
  moreover have "\<V>(fragm [l\<mapsto>(dq,to_ag (Some v))]) \<turnstile> \<upharpoonleft>(valid(fragm [l\<mapsto>(dq,to_ag (Some v))]))"
    using discrete_valid[of "fragm [l\<mapsto>(dq,to_ag (Some v))]"] upred_entail_eq_def 
    by (auto simp: valid_raw_prod_def \<epsilon>_n_valid valid_def)
  ultimately have "((l \<mapsto>{dq} v)::('a,'v option,'c) heapCmra iprop) \<turnstile> \<upharpoonleft>(valid dq)" 
    by (auto simp: frag_heap_valid intro: upred_entails_trans)
  from upred_wand_holdsI [OF this] show ?thesis .
qed

lemma points_to_agree: "upred_holds ((l \<mapsto>{dq1} (v1::'v::discrete)) -\<^emph> 
  ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> \<upharpoonleft>(v1 = v2))"
proof -
  have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> 
    \<V>((fragm [l\<mapsto>(dq1, to_ag (Some v1))],\<epsilon>::'c)\<cdot>(fragm [l\<mapsto>(dq2, to_ag (Some v2))],\<epsilon>)))"
    apply (auto simp: points_to_def) using own_valid2 by blast
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> 
    \<V>((fragm ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))]),\<epsilon>::'c)))"
    by (auto simp: heap_op \<epsilon>_left_id op_prod_def op_auth_def op_option_def)    
  then have v:"upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> 
    \<V>(fragm ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))])))"
    by (auto simp: upred_valid_def valid_def valid_raw_prod_def \<epsilon>_n_valid sprop_conj.rep_eq valid_raw_auth_def)
  have "valid (fragm [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))]) \<Longrightarrow> 
      valid (to_ag (Some v1) \<cdot> to_ag (Some v2))"
    by (auto simp: valid_def valid_raw_fun.rep_eq op_prod_def valid_raw_option_def prod_n_valid_def 
        split: option.splits) (metis)
  from d_ag_agree[OF this] have "valid (fragm [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))]) \<Longrightarrow> v1=v2"
    by (auto simp: to_ag_def Abs_ag_inject)
  from upred_entails_wand_holdsR2[OF 
    pure_entailsI[of "valid (fragm [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))])" "v1=v2", OF this, simplified]
    upred_entails_wand_holdsR2[OF upred_entail_eqL[OF discrete_valid] v]]
  show ?thesis .
qed

lemma points_to_combine_same:"((l \<mapsto>{dq1} v)::('a,'v::discrete option,'c) heapCmra iprop) \<^emph> (l \<mapsto>{dq2} v) \<turnstile> (l \<mapsto>{dq1 \<cdot> dq2} v)"
  apply (unfold points_to_def)
  apply (unfold heap_op_val_eq[symmetric])
  by (rule upred_entail_eqR[OF own_op, of "(fragm [l \<mapsto> (dq1, to_ag (Some v))],\<epsilon>::'c)" 
      "(fragm [l \<mapsto> (dq2, to_ag (Some v))],\<epsilon>)", unfolded op_prod_def, simplified, 
      unfolded \<epsilon>_left_id auth_frag_op[symmetric]])

lemma points_to_combine: "upred_holds ((l\<mapsto>{dq1} (v1::'v::discrete)) -\<^emph> 
  ((l \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> (l\<mapsto>{dq1\<cdot>dq2} v1) \<^emph> \<upharpoonleft>(v1=v2))"
  apply (rule upred_wand_holds2I)
  apply (rule upred_sep_pure)
  apply (rule entails_pure_extend[OF upred_wandE[OF upred_wand_holdsE[OF points_to_agree]]])
  apply (unfold points_to_def)[1]
  apply (metis points_to_def points_to_combine_same)
  by (rule upred_wandE[OF upred_wand_holdsE[OF points_to_agree]])

lemma points_to_frac_ne: 
  assumes "\<not> (valid (dq1\<cdot>dq2))"
  shows "upred_holds ((l1 \<mapsto>{dq1} (v1::'v::discrete)) -\<^emph> 
    ((l2 \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> \<upharpoonleft>(l1\<noteq>l2))"
proof -
  have valid_drop : 
    "valid ((fragm [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (fragm [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c)) =
      valid ((fragm [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (fragm [l2\<mapsto>(dq2,to_ag (Some v2))]))"
    by (auto simp: camera_valid_op prod_valid_def op_prod_def \<epsilon>_left_id \<epsilon>_valid)
  have "\<V>(((fragm [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (fragm [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c))) \<turnstile>
    \<upharpoonleft>(valid ((fragm [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (fragm [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c)))"
    apply (auto simp: op_prod_def)
    apply (auto simp: prod_valid_def \<epsilon>_left_id \<epsilon>_valid upred_valid_def)
    apply (auto simp: valid_raw_prod_def sprop_conj.rep_eq \<epsilon>_n_valid)
    by (rule upred_entail_eqL[OF discrete_valid[unfolded upred_valid_def], simplified])    
  then have base: "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> 
    ((l2 \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> 
    \<upharpoonleft>(valid ((fragm [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c) \<cdot> (fragm [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c))))"
    using upred_wand_holds2I[OF upred_entails_trans[OF upred_wand_holds2E[OF own_valid2]]]
    by (smt (verit, del_insts) points_to_def)
  from assms have "valid ((fragm [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (fragm [l2\<mapsto>(dq2,to_ag (Some v2))])) 
    \<Longrightarrow> l1\<noteq>l2"
    apply (auto simp: valid_def auth_frag_op[symmetric] heap_op op_prod_def)
    apply (auto simp: valid_raw_prod_def Abs_ag_inverse valid_raw_fun.rep_eq valid_raw_option_def  split: option.splits)
    by (metis sprop_conj.rep_eq)    
  then have "\<upharpoonleft>(valid ((fragm [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (fragm [l2\<mapsto>(dq2,to_ag (Some v2))]))) \<turnstile>
    \<upharpoonleft>(l1\<noteq>l2)" using pure_entailsI by blast
  with valid_drop have 
    "\<upharpoonleft>(valid ((fragm [l1\<mapsto>(dq1,to_ag (Some v1))],\<epsilon>::'c)\<cdot>(fragm [l2\<mapsto>(dq2,to_ag (Some v2))],\<epsilon>::'c))) \<turnstile>
    \<upharpoonleft>(l1\<noteq>l2)" by simp
    from upred_entails_wand_holdsR2[OF this base] show ?thesis .
qed

lemma points_to_ne: "upred_holds ((l1\<mapsto>\<^sub>u(v1::'v::discrete)) -\<^emph> 
  ((l2 \<mapsto>{dq2} v2)::('a,'v option,'c::ucamera) heapCmra iprop) -\<^emph> \<upharpoonleft>(l1\<noteq>l2))"
  by (rule points_to_frac_ne[OF dfrac_not_valid_own])

definition to_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<rightharpoonup>(dfrac\<times>'v option ag))" where
  "to_heap h = (\<lambda>op. map_option (\<lambda>v::'v. (DfracOwn 1,to_ag (Some v))) op) \<circ> h"

definition to_heap_op :: "('l\<rightharpoonup>('v::ofe option)) \<Rightarrow> ('l\<rightharpoonup>(dfrac\<times>'v option ag))" where
  "to_heap_op h = (\<lambda>op. map_option (\<lambda>v::'v option. (DfracOwn 1,to_ag  v)) op) \<circ> h"
  
definition heapInv :: "('l,('v::ofe) option,'c::ucamera) heapCmra iprop" where
  "heapInv \<equiv> \<exists>\<^sub>u(\<lambda>h. (Own\<^sub>h(full (to_heap h))) \<^emph> (sep_map_heap h (\<lambda>(l,v). l\<mapsto>\<^sub>uv)))"
end
end