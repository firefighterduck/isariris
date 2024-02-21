theory AuthHeap
imports DerivedConstructions Frac BaseLogicShallow View Own ProofSearchPredicates ProphMap
begin


subsubsection \<open>View based heap\<close>
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

context
fixes get_heap :: "gname \<Rightarrow> 'a::ucamera \<Rightarrow> ('l,'v::ofe option) heap option"
  and put_heap
assumes heap_inG: "inG get_heap put_heap"
begin

text \<open>Unique name for singleton heap camera\<close>
definition "heap_name :: gname \<equiv> 0"

lemma heap_frag_valid: "\<V>(inG.return_cmra put_heap \<gamma> (\<circle>V [k\<mapsto>(dq,to_ag v)])) \<turnstile> \<upharpoonleft>(valid dq)"
  by (auto simp: upred_valid.rep_eq upred_entails.rep_eq upred_pure.rep_eq inG.return_n_valid[OF heap_inG] 
    valid_def mview_frag_def valid_raw_map_view.rep_eq map_view_rel_def)

lemma heap_op: "[l\<mapsto>(dq1, to_ag v1)]\<cdot>[l\<mapsto>(dq2, to_ag v2)] = [l\<mapsto>(dq1, to_ag v1)\<cdot>(dq2, to_ag v2)]"
  by (auto simp: op_fun_def op_option_def)

lemma heap_op_val_eq: "[l\<mapsto>(dq1, to_ag v)]\<cdot>[l\<mapsto>(dq2, to_ag v)] = [l\<mapsto>(dq1\<cdot>dq2, to_ag v)]" 
  unfolding heap_op by (auto simp: op_prod_def op_ag_def to_ag_def Rep_ag_inverse)

lemma heap_valid: "\<V>(inG.return_cmra put_heap \<gamma> h) \<turnstile> \<V>(h::('l,'v option) heap)"
  by (simp add: upred_valid_def upred_entails.rep_eq Abs_upred_f_inverse inG.return_n_valid[OF heap_inG])

text \<open>Heap camera operations\<close>
abbreviation own_heap :: "('l,'v option) heap \<Rightarrow> 'a upred_f" ("Own\<^sub>h _") where
   "own_heap h \<equiv> own put_heap heap_name h"

definition own_heap_auth :: "frac \<Rightarrow> ('l,'v option) fmap \<Rightarrow> 'a upred_f" where
  "own_heap_auth q m \<equiv> Own\<^sub>h(map_view_auth (DfracOwn q) m)"
  
text \<open>Because our heap camera does not contain meta tokens, this proposition is just about owning a heap.\<close>
definition heap_interp :: "('l,'v option) fmap \<Rightarrow> 'a upred_f" where
  "heap_interp \<sigma> \<equiv> own_heap_auth 1 \<sigma>" 
 
definition points_to :: "'l \<Rightarrow> dfrac \<Rightarrow> 'v \<Rightarrow> 'a upred_f" where
  "points_to l dq v = Own\<^sub>h(map_view_frag l dq (Some v))"
abbreviation points_to_disc :: "'l \<Rightarrow> 'v \<Rightarrow> 'a upred_f" where 
  "points_to_disc \<equiv> \<lambda>l v. points_to l DfracDiscarded v"
abbreviation points_to_own :: "'l \<Rightarrow> frac \<Rightarrow> 'v \<Rightarrow> 'a upred_f" where
  "points_to_own \<equiv> \<lambda>l p v. points_to l (DfracOwn p) v"
abbreviation points_to_full :: "'l \<Rightarrow> 'v \<Rightarrow> 'a upred_f" where
  "points_to_full \<equiv> \<lambda>l v. points_to_own l 1 v"
  
lemma points_to_valid: 
  "(points_to l dq v) -\<^emph> \<upharpoonleft>(valid dq)"
proof -
  have "(points_to l dq v) \<turnstile> \<V>(inG.return_cmra put_heap heap_name (\<circle>V [l\<mapsto>(dq,to_ag (Some v))]))" 
    by (auto simp: points_to_def inG.own_valid'[OF heap_inG] map_view_frag_def)
  moreover have "\<V>(inG.return_cmra put_heap heap_name (\<circle>V [l\<mapsto>(dq,to_ag (Some v))])) \<turnstile> 
    \<V>((\<circle>V [l\<mapsto>(dq,to_ag (Some v))])::('l,'v option) heap)"
    using heap_valid by blast
  ultimately have "(points_to l dq v) \<turnstile> \<upharpoonleft>(valid dq)"
    using heap_frag_valid upred_entails_trans by blast
  from upred_wand_holdsI [OF this] show ?thesis .
  qed
end

context
fixes get_heap :: "gname \<Rightarrow> 'a::ucamera \<Rightarrow> ('l,'v::discrete option) heap option"
  and put_heap
assumes heap_inG: "inG get_heap put_heap"
begin

abbreviation "points_to' \<equiv> points_to put_heap"
abbreviation "points_to_disc' \<equiv> points_to_disc put_heap"
abbreviation "points_to_own' \<equiv> points_to_own put_heap"
abbreviation "points_to_full' \<equiv> points_to_full put_heap"

notation points_to' ("_ \<mapsto>{_} _" 60)
notation points_to_disc' (infix "\<mapsto>\<box>" 60)
notation points_to_own' ("_\<mapsto>{#_}_" 60)
notation points_to_full' (infix "\<mapsto>\<^sub>u" 60)

lemma points_to_agree: "upred_holds ((((l::'l) \<mapsto>{dq1} (v1::'v))::'a upred_f) -\<^emph> ((l \<mapsto>{dq2} v2) -\<^emph> \<upharpoonleft>(v1 = v2)))"
proof -
  have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)) -\<^emph> 
    \<V>(inG.return_cmra put_heap heap_name (\<circle>V [l\<mapsto>(dq1, to_ag (Some v1))]) \<cdot> 
    inG.return_cmra put_heap heap_name (\<circle>V [l\<mapsto>(dq2, to_ag (Some v2))])))"
    apply (simp add: points_to_def[OF heap_inG]) by (metis heap_inG inG.own_def map_view_frag_def upred_own_valid2)
  then have "upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)) -\<^emph> 
    \<V>(inG.return_cmra put_heap heap_name (\<circle>V ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))]))))"
    by (auto simp: inG.return_op[OF heap_inG, symmetric] mview_frag_def op_map_view_def
      op_option_def)
  then have v:"upred_holds ((l \<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2)) -\<^emph> 
    \<V>(\<circle>V ([l\<mapsto>(dq1, to_ag (Some v1))\<cdot>(dq2, to_ag (Some v2))])))"
    using upred_entails_wand_holdsR2[OF heap_valid, OF heap_inG] by blast
  have "valid (\<circle>V [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))]) \<Longrightarrow> 
    valid (to_ag (Some v1) \<cdot> to_ag (Some v2))"
    apply (auto simp: valid_def mview_frag_def valid_raw_map_view.rep_eq map_view_rel_def op_prod_def
      split: option.splits)
    by (metis n_valid_ne ofe_sym to_ag_n_valid)
  from d_ag_agree[OF this] have "valid (\<circle>V [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))]) \<Longrightarrow> v1=v2"
    by (auto simp: to_ag_def Abs_ag_inject)
  from upred_entails_wand_holdsR2[OF 
    pure_entailsI[of "valid (\<circle>V [l \<mapsto> (dq1, to_ag (Some v1)) \<cdot> (dq2, to_ag (Some v2))])" "v1=v2", OF this, simplified]
    upred_entails_wand_holdsR2[OF upred_entail_eqL[OF discrete_valid] v]]
  show ?thesis .
qed

lemma points_to_combine_same:"((l \<mapsto>{dq1} v)) \<^emph> (l \<mapsto>{dq2} v) \<turnstile> (l \<mapsto>{dq1 \<cdot> dq2} v)"
  apply (unfold points_to_def[OF heap_inG] map_view_frag_def mview_frag_def)
  apply (unfold heap_op_val_eq[OF heap_inG,symmetric])
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF inG.own_op[OF heap_inG]]])
  by (auto simp: op_map_view_def op_option_def)

lemma points_to_split: "(l \<mapsto>{dq1 \<cdot> dq2} v) \<turnstile> ((l \<mapsto>{dq1} v)) \<^emph> (l \<mapsto>{dq2} v)"
apply (unfold points_to_def[OF heap_inG] map_view_frag_def mview_frag_def)
apply (unfold heap_op_val_eq[OF heap_inG,symmetric])
apply (rule upred_entails_trans[OF _ upred_entail_eqL[OF inG.own_op[OF heap_inG]]])
by (auto simp: op_map_view_def op_option_def)
  
lemma points_to_combine: "upred_holds ((l\<mapsto>{dq1} v1) -\<^emph> ((l \<mapsto>{dq2} v2) -\<^emph> ((l\<mapsto>{dq1\<cdot>dq2} v1) \<^emph> \<upharpoonleft>(v1=v2))))"
  apply (rule upred_wand_holds2I)
  apply (rule upred_sep_pure)
  apply (rule entails_pure_extend[OF upred_wandE[OF upred_wand_holdsE[OF points_to_agree]]])
  using points_to_combine_same points_to_def[OF heap_inG] apply fastforce
  by (simp add: points_to_agree upred_wand_holds2E)

lemma points_to_frac_ne: 
  assumes "\<not> (valid (dq1\<cdot>dq2))"
  shows "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> ((l2 \<mapsto>{dq2} v2) -\<^emph> \<upharpoonleft>(l1\<noteq>l2)))"
proof -
  have valid_drop : 
    "valid (inG.return_cmra put_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
    inG.return_cmra put_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))])) =
      valid ((\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))"
    by (simp add: valid_def inG.return_n_valid[OF heap_inG] inG.return_op[OF heap_inG, symmetric])
  have "\<V>((inG.return_cmra put_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
      inG.return_cmra put_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))) 
    \<turnstile> \<upharpoonleft>(valid (inG.return_cmra put_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
      inG.return_cmra put_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))])))"
    apply (simp add: upred_pure.rep_eq upred_entails.rep_eq upred_valid.rep_eq
      valid_def inG.return_n_valid[OF heap_inG] inG.return_op[OF heap_inG, symmetric])
    using dcamera_valid_iff by auto
  then have base: "upred_holds ((l1 \<mapsto>{dq1} v1) -\<^emph> ((l2 \<mapsto>{dq2} v2)) -\<^emph> 
    \<upharpoonleft>(valid (inG.return_cmra put_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
    inG.return_cmra put_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))))"
    using upred_wand_holds2I[OF upred_entails_trans[OF upred_wand_holds2E[OF upred_own_valid2]]] 
      points_to_def[OF heap_inG] by (metis heap_inG inG.own_def map_view_frag_def)
  from assms have "valid ((\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))])) 
    \<Longrightarrow> l1\<noteq>l2"
    apply (simp add: valid_def)
    apply (rule notI)
    apply (simp add: mview_frag_def op_map_view_def heap_op op_prod_def op_option_def)
    apply (auto simp: valid_raw_map_view.rep_eq map_view_rel_def split: option.splits)
    by (metis assms)
  then have "\<upharpoonleft>(valid ((\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))) \<turnstile>
    \<upharpoonleft>(l1\<noteq>l2)" using pure_entailsI by blast
  with valid_drop have 
    "\<upharpoonleft>(valid (inG.return_cmra put_heap heap_name (\<circle>V [l1\<mapsto>(dq1,to_ag (Some v1))]) \<cdot> 
    inG.return_cmra put_heap heap_name (\<circle>V [l2\<mapsto>(dq2,to_ag (Some v2))]))) 
    \<turnstile> \<upharpoonleft>(l1\<noteq>l2)" by simp
    from upred_entails_wand_holdsR2[OF this base] show ?thesis .
qed

lemma points_to_ne: "upred_holds ((l1\<mapsto>\<^sub>uv1) -\<^emph> ((l2 \<mapsto>{dq2} v2)) -\<^emph> \<upharpoonleft>(l1\<noteq>l2))"
by (rule points_to_frac_ne[OF dfrac_not_valid_own])

lemma timeless_points_to [timeless_rule, log_prog_rule]: "timeless (l\<mapsto>{p}v)"
  unfolding points_to_def[OF heap_inG] 
  apply (auto simp: inG.own_def[OF heap_inG] upred_own.rep_eq dcamera_val_def discrete_val_def 
    inG.return_ne[OF heap_inG] ofe_refl valid_def inG.return_n_valid[OF heap_inG] ofe_limit
    intro!: own_timeless')
  apply prefer_last
  using dcamera_valid_iff apply blast
  by (metis (full_types) d_equiv heap_inG inG.return_ne inG.return_ne2)+
  
lemma points_to_lookup: "heap_interp put_heap h \<^emph> (l\<mapsto>\<^sub>uv) \<turnstile> \<upharpoonleft>(fmlookup h l = Some (Some v))"
proof -
  have "heap_interp put_heap h \<^emph> (l\<mapsto>\<^sub>uv) \<turnstile> own_heap put_heap (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l (DfracOwn 1) (Some v))"
    unfolding heap_interp_def[OF heap_inG] points_to_def[OF heap_inG] own_heap_auth_def[OF heap_inG]
    apply (rule upred_entails_trans[OF upred_entail_eqR[OF inG.own_op[OF heap_inG]]])
    by (auto simp: op_prod_def \<epsilon>_left_id)
  then have "heap_interp put_heap h \<^emph> (l\<mapsto>\<^sub>uv) \<turnstile> \<V> (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l (DfracOwn 1) (Some v))"
    using inG.own_valid[OF heap_inG] heap_valid[OF heap_inG] upred_entails_trans by blast
  then have 1: "heap_interp put_heap h \<^emph> (l\<mapsto>\<^sub>uv) \<turnstile> \<upharpoonleft>(valid (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l (DfracOwn 1) (Some v)))"
    using discrete_valid upred_entail_eqL upred_entails_trans by blast
  have "valid (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l (DfracOwn 1) (Some v)) \<Longrightarrow> fmlookup h l = Some (Some v)"
    unfolding valid_def view_both_valid map_view_auth_def map_view_frag_def map_view_rel_def 
    apply auto by (metis d_equiv to_ag_n_equiv)
  then have "\<upharpoonleft>(valid (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l (DfracOwn 1) (Some v))) \<turnstile> \<upharpoonleft>(fmlookup h l = Some (Some v))"
    by fastforce
  with 1 show ?thesis by (rule upred_entails_trans)
qed

lemma points_to_lookup2: "heap_interp put_heap h \<^emph> (l\<mapsto>{dq}v) \<turnstile> \<upharpoonleft>(fmlookup h l = Some (Some v))"
proof -
  have "heap_interp put_heap h \<^emph> (l\<mapsto>{dq}v) \<turnstile> own_heap put_heap (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l dq (Some v))"
    unfolding heap_interp_def[OF heap_inG] points_to_def[OF heap_inG] own_heap_auth_def[OF heap_inG]
    apply (rule upred_entails_trans[OF upred_entail_eqR[OF inG.own_op[OF heap_inG]]])
    by (auto simp: op_prod_def \<epsilon>_left_id)
  then have "heap_interp put_heap h \<^emph> (l\<mapsto>{dq}v) \<turnstile> \<V> (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l dq (Some v))"
    using inG.own_valid[OF heap_inG] heap_valid[OF heap_inG] upred_entails_trans by blast
  then have 1: "heap_interp put_heap h \<^emph> (l\<mapsto>{dq}v) \<turnstile> \<upharpoonleft>(valid (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l dq (Some v)))"
    using discrete_valid upred_entail_eqL upred_entails_trans by blast
  have "valid (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l dq (Some v)) \<Longrightarrow> fmlookup h l = Some (Some v)"
    unfolding valid_def view_both_valid map_view_auth_def map_view_frag_def map_view_rel_def 
    apply auto by (metis d_equiv to_ag_n_equiv)
  then have "\<upharpoonleft>(valid (map_view_auth (DfracOwn 1) h \<cdot> map_view_frag l dq (Some v))) \<turnstile> \<upharpoonleft>(fmlookup h l = Some (Some v))"
    by fastforce
  with 1 show ?thesis by (rule upred_entails_trans)
qed  
end

subsubsection \<open>Prophecy map camera\<close>
context
fixes get_prophm :: "gname \<Rightarrow> 'a::ucamera \<Rightarrow> ('p, 'vs::ofe) proph_mapGS option"
  and put_prophm
assumes prophm_inG: "inG get_prophm put_prophm"
begin
text \<open>Unique name for singleton \<^typ>\<open>('p, 'vs) proph_mapGS\<close> camera\<close>
definition "proph_map_name :: gname \<equiv> 4"

abbreviation proph_own :: "('p, 'vs) proph_mapGS \<Rightarrow> 'a upred_f" ("Own\<^sub>p _") where
  "proph_own pm \<equiv> own put_prophm proph_map_name pm"

abbreviation own_proph_auth :: "frac \<Rightarrow> ('p, 'vs list) fmap \<Rightarrow> 'a upred_f" where
  "own_proph_auth q m \<equiv> Own\<^sub>p(map_view_auth (DfracOwn q) m)" 
  
definition proph_map_interp :: "('p \<times> 'vs) list \<Rightarrow> 'p fset \<Rightarrow> 'a upred_f" where
  "proph_map_interp pvs ps \<equiv> \<exists>\<^sub>u R. (\<upharpoonleft>(proph_resolves_in_list R pvs \<and> fmdom R |\<subseteq>| ps))
    \<^emph> (own_proph_auth 1 R)"

definition proph :: "'p \<Rightarrow> 'vs list \<Rightarrow> 'a upred_f" where
  "proph p vs = Own\<^sub>p(map_view_frag p (DfracOwn 1) vs)"
end
end