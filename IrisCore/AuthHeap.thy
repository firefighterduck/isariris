theory AuthHeap
imports DerivedConstructions Frac BaseLogicShallow Misc
begin

subsubsection \<open>View based heap\<close>

text \<open>Unique name for singleton heap camera\<close>
definition "heap_name :: gname \<equiv> 0"

type_synonym ('l,'v) heap = "('l,'v) map_view"

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
    from f' assms(2) have "valid f'" apply (simp add: valid_def) 
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

lemma heap_frag_valid: "\<V>(constr_heap \<gamma> (\<circle>V [k\<mapsto>(dq,to_ag v)])) \<turnstile> \<upharpoonleft>(valid dq)"
  by transfer' 
  (auto simp: constr_heap_def prod_n_valid_def \<epsilon>_n_valid view_frag_def valid_raw_map_view.rep_eq 
    map_view_rel_def split: option.splits)

lemma heap_op: "[l\<mapsto>(dq1, to_ag v1)]\<cdot>[l\<mapsto>(dq2, to_ag v2)] = [l\<mapsto>(dq1, to_ag v1)\<cdot>(dq2, to_ag v2)]"
  by (auto simp: op_fun_def op_option_def)

lemma heap_op_val_eq: "[l\<mapsto>(dq1, to_ag v)]\<cdot>[l\<mapsto>(dq2, to_ag v)] = [l\<mapsto>(dq1\<cdot>dq2, to_ag v)]" 
  unfolding heap_op by (auto simp: op_prod_def op_ag_def to_ag_def Rep_ag_inverse)

lemma iprop_heap_valid: "\<V>(constr_heap \<gamma> h) \<turnstile> \<V>(h::heap_lang_heap)"
  apply (simp add: upred_valid_def upred_entails.rep_eq Abs_upred_f_inverse constr_heap_def)
  using prod_n_valid_snd[OF prod_n_valid_snd[OF prod_n_valid_snd[OF prod_n_valid_snd[OF prod_n_valid_snd]]]] 
  by fastforce

text \<open>Heap camera operations\<close>
abbreviation own_heap :: "heap_lang_heap \<Rightarrow> iprop" ("Own\<^sub>h _") where
   "own_heap h \<equiv> Own(constr_heap heap_name h)"

definition own_heap_auth :: "frac \<Rightarrow> (loc,val option) fmap \<Rightarrow> iprop" where
  "own_heap_auth q m \<equiv> Own\<^sub>h(map_view_auth (DfracOwn q) m)"
  
text \<open>Because our heap camera does not contain meta tokens, this proposition is just about owning a heap.\<close>
definition heap_interp :: "(loc,val option) fmap \<Rightarrow> iprop" where
  "heap_interp \<sigma> \<equiv> own_heap_auth 1 \<sigma>" 
 
definition points_to :: "loc \<Rightarrow> dfrac \<Rightarrow> val \<Rightarrow> iprop" where
  "points_to l dq v = Own\<^sub>h(map_view_frag l dq (Some v))"
abbreviation points_to_disc :: "loc \<Rightarrow> val \<Rightarrow> iprop" where 
  "points_to_disc \<equiv> \<lambda>l v. points_to l DfracDiscarded v"
abbreviation points_to_own :: "loc \<Rightarrow> frac \<Rightarrow> val \<Rightarrow> iprop" where
  "points_to_own \<equiv> \<lambda>l p v. points_to l (DfracOwn p) v"
abbreviation points_to_full :: "loc \<Rightarrow> val \<Rightarrow> iprop" where
  "points_to_full \<equiv> \<lambda>l v. points_to_own l 1 v"
  
notation points_to ("_ \<mapsto>{_} _" 60)
notation points_to_disc (infix "\<mapsto>\<box>" 60)
notation points_to_own ("_\<mapsto>{#_}_" 60)
notation points_to_full (infix "\<mapsto>\<^sub>u" 60)

context assumes "SORT_CONSTRAINT('c::ucamera)" begin 

lemma points_to_valid: 
  "(l \<mapsto>{dq} v) -\<^emph> \<upharpoonleft>(valid dq)"
proof -
  have "(l \<mapsto>{dq} v) \<turnstile> \<V>(constr_heap heap_name (\<circle>V [l\<mapsto>(dq,to_ag (Some v))]))" 
    by (auto simp: points_to_def own_valid map_view_frag_def)
  moreover have "\<V>(constr_heap heap_name (\<circle>V [l\<mapsto>(dq,to_ag (Some v))])) \<turnstile> 
    \<V>((\<circle>V [l\<mapsto>(dq,to_ag (Some v))])::heap_lang_heap)"
    using iprop_heap_valid by blast
  ultimately have "(l \<mapsto>{dq} v) \<turnstile> \<upharpoonleft>(valid dq)"
    using heap_frag_valid upred_entails_trans by blast
  from upred_wand_holdsI [OF this] show ?thesis .
qed

lemma points_to_agree: "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2) -\<^emph> \<upharpoonleft>(v1 = v2)))"
proof -
  have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)) -\<^emph> 
    \<V>(constr_heap heap_name (\<circle>V [l\<mapsto>(dq1, to_ag (Some v1))]) \<cdot> 
    constr_heap heap_name (\<circle>V [l\<mapsto>(dq2, to_ag (Some v2))])))"
    apply (simp add: points_to_def) using own_valid2 by (metis map_view_frag_def)
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)) -\<^emph> 
    \<V>(constr_heap heap_name (\<circle>V ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))]))))"
    apply (simp add: \<epsilon>_left_id op_prod_def constr_heap_def op_map_view_def map_view_auth_proj_def
      \<epsilon>_map_view_def map_view_frag_proj_def view_frag_def heap_op)
    by (auto simp: op_option_def)   
  then have v:"upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)) -\<^emph> 
    \<V>(\<circle>V ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))])))"
    using  upred_entails_wand_holdsR2[OF iprop_heap_valid] by blast
  have "valid (\<circle>V [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))]) \<Longrightarrow> 
      valid (to_ag (Some v1) \<cdot> to_ag (Some v2))"
    apply (auto simp: valid_def view_frag_def valid_raw_map_view.rep_eq  map_view_rel_def op_prod_def
        split: option.splits)
    by (metis d_equiv to_ag_n_valid)
  from d_ag_agree[OF this] have "valid (\<circle>V [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))]) \<Longrightarrow> v1=v2"
    by (auto simp: to_ag_def Abs_ag_inject)
  from upred_entails_wand_holdsR2[OF 
    pure_entailsI[of "valid (\<circle>V [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))])" "v1=v2", OF this, simplified]
    upred_entails_wand_holdsR2[OF upred_entail_eqL[OF discrete_valid] v]]
  show ?thesis .
qed

lemma points_to_combine_same:"((l \<mapsto>{dq1} v)) \<^emph> (l \<mapsto>{dq2} v) \<turnstile> (l \<mapsto>{dq1 \<cdot> dq2} v)"
  apply (unfold points_to_def map_view_frag_def view_frag_def)
  apply (unfold heap_op_val_eq[symmetric])
  apply (unfold constr_heap_def)
  apply simp
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF own_op]])
  by (auto simp: op_map_view_def op_prod_def \<epsilon>_left_id map_view_auth_proj_def map_view_frag_proj_def
    \<epsilon>_map_view_def op_option_def \<epsilon>_option_def)

lemma points_to_combine: "upred_holds ((l\<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2) -\<^emph> ((l\<mapsto>{dq1\<cdot>dq2} v1) \<^emph> \<upharpoonleft>(v1=v2))))"
  apply (rule upred_wand_holds2I)
  apply (rule upred_sep_pure)
  apply (rule entails_pure_extend[OF upred_wandE[OF upred_wand_holdsE[OF points_to_agree]]])
  apply (unfold points_to_def)[1]
  apply (metis points_to_def points_to_combine_same)
  by (rule upred_wandE[OF upred_wand_holdsE[OF points_to_agree]])

lemma points_to_frac_ne: 
  assumes "\<not> (valid (dq1\<cdot>dq2))"
  shows "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> ((l2 \<mapsto>{dq2} v2) -\<^emph> \<upharpoonleft>(l1\<noteq>l2)))"
proof -
  have valid_drop : 
    "valid (constr_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
    constr_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))])) =
      valid ((\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))"
    by (simp add: op_prod_def \<epsilon>_left_id \<epsilon>_valid prod_valid_def constr_heap_def)
  have "\<V>((constr_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
      constr_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))) 
    \<turnstile> \<upharpoonleft>(valid (constr_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
      constr_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))])))"
    apply (simp add: op_prod_def \<epsilon>_left_id constr_heap_def)
    apply (simp add: upred_pure.rep_eq upred_entails.rep_eq upred_valid.rep_eq)
    apply (simp add: prod_n_valid_fun_def prod_valid_def \<epsilon>_valid \<epsilon>_n_valid)
    using dcamera_valid_iff by auto
  then have base: "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> ((l2 \<mapsto>{dq2} v2)) -\<^emph> 
    \<upharpoonleft>(valid (constr_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
    constr_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))))"
    using upred_wand_holds2I[OF upred_entails_trans[OF upred_wand_holds2E[OF own_valid2]]] points_to_def
    by (smt (verit) map_view_frag_def)
  from assms have "valid ((\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))])) 
    \<Longrightarrow> l1\<noteq>l2"
    apply (simp add: valid_def)
    apply (rule notI)
    apply (simp add: view_frag_def op_map_view_def heap_op op_prod_def op_option_def)
    apply (auto simp: valid_raw_map_view.rep_eq map_view_rel_def split: option.splits)
    by (metis assms)
  then have "\<upharpoonleft>(valid ((\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))) \<turnstile>
    \<upharpoonleft>(l1\<noteq>l2)" using pure_entailsI by blast
  with valid_drop have 
    "\<upharpoonleft>(valid (constr_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
    constr_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))) 
    \<turnstile> \<upharpoonleft>(l1\<noteq>l2)" by simp
    from upred_entails_wand_holdsR2[OF this base] show ?thesis .
qed

lemma points_to_ne: "upred_holds ((l1\<mapsto>\<^sub>uv1) -\<^emph> ((l2 \<mapsto>{dq2} v2)) -\<^emph> \<upharpoonleft>(l1\<noteq>l2))"
by (rule points_to_frac_ne[OF dfrac_not_valid_own])

lemma timeless_points_to [timeless_rule]: "timeless (l\<mapsto>{p}v)"
  unfolding points_to_def constr_heap_def timeless_def except_zero_def
  by transfer' (auto simp: singleton_map_n_incl d_equiv)
end

subsubsection \<open>Prophecy map camera\<close>

text \<open>Unique name for singleton proph_map camera\<close>
definition "proph_map_name :: gname \<equiv> 4"

abbreviation proph_own :: "heap_lang_proph_map \<Rightarrow> iprop" ("Own\<^sub>p _") where
  "proph_own pm \<equiv> Own(constr_proph proph_map_name pm)"

abbreviation own_proph_auth :: "frac \<Rightarrow> heap_lang_proph_map_raw \<Rightarrow> iprop" where
  "own_proph_auth q m \<equiv> Own\<^sub>p(map_view_auth (DfracOwn q) m)" 
  
definition proph_map_interp :: "heap_lang_proph_val_list \<Rightarrow> proph_id fset \<Rightarrow> iprop" where
  "proph_map_interp pvs ps \<equiv> \<exists>\<^sub>u R. (\<upharpoonleft>(proph_resolves_in_list R pvs \<and> fmdom R |\<subseteq>| ps))
    \<^emph> (own_proph_auth 1 R)"

definition proph :: "proph_id \<Rightarrow> (val\<times>val) list \<Rightarrow> iprop" where
  "proph p vs = Own\<^sub>p(map_view_frag p (DfracOwn 1) vs)"
end