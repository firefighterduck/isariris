theory Spanning
imports Mon "../HeapLang/Par" "../HeapLang/WeakestPrecondition"
begin

subsection \<open> Spanning Tree \<close>
text \<open> Based on \<^url>\<open>https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/spanning_tree/spanning.v\<close> \<close>

definition try_mark :: val where "try_mark \<equiv> 
  V\<lambda> Some ''y'': let: Some ''e'' := Fst (!(V ''y'')) in (CAS (V ''e'') FalseE TrueE) endlet"

definition unmark_fst :: val where "unmark_fst \<equiv>
  V\<lambda> Some ''y'': let: Some ''e'' := !(V ''y'') in 
  ((V ''y'') \<leftarrow> (Pair (Fst (V ''e'')) (Pair NoneE (Snd (Snd (V ''e'')))))) endlet"

definition unmark_snd :: val where "unmark_snd \<equiv>
  V\<lambda> Some ''y'': let: Some ''e'' := !(V ''y'') in 
  ((V ''y'') \<leftarrow> (Pair (Fst (V ''e'')) (Pair (Fst (Snd (V (''e'')))) NoneE))) endlet"

definition span :: val where "span \<equiv>
  RecV (Some ''span'') (Some ''x'')
  match: (V ''x'') with
  NoneCase \<Rightarrow> FalseE
  | SomeCase (Some ''y'') \<Rightarrow> 
    if: App (Val try_mark) (V ''y'') then
      let: Some ''e'' := !(V ''y'') in
      let: Some ''rs'' := 
        (App (V ''span'') (Fst (Snd (V ''e'')))) ||| (App (V ''span'') (Snd (Snd (V ''e'')))) in
      if: UnOp NegOp (Fst (V ''rs'')) then App (Val unmark_fst) (V ''y'') else UnitE endif ;;
      if: UnOp NegOp (Snd (V ''rs'')) then App (Val unmark_snd) (V ''y'') else UnitE endif ;;
      TrueE endlet endlet
    else FalseE
    endif
  endmatch"
  
subsubsection \<open>Proofs\<close>
context wp_rules begin  
lemma wp_try_mark:
assumes "x\<in>fmdom' g"
shows "(graph_ctxt \<kappa> g Mrk) \<^emph> (own_graphUR q fmempty) \<^emph> (cinv_own \<kappa> k) \<turnstile>
  WP (App (of_val try_mark) (of_val #[x])) 
  {{ \<lambda>v.
    ((\<upharpoonleft>(v=#[True])) \<^emph> (\<exists>\<^sub>u u. (((\<upharpoonleft>(fmlookup g x = Some u)) \<^emph> own_graphUR q (x [\<mapsto>\<^sub>g] u)))) \<^emph> is_marked x \<^emph> cinv_own \<kappa> k)
    \<or>\<^sub>u ((\<upharpoonleft>(v=#[False])) \<^emph> own_graphUR q fmempty \<^emph> is_marked x \<^emph> cinv_own \<kappa> k) 
  }}"
  apply (auto simp: try_mark_def subst'_def intro!: wp_pure[OF pure_exec_beta] wp_let_bind'[where C=Fst])
  unfolding graph_ctxt_def
  apply (iMod rule: cinv_acc[OF subset_UNIV])
  apply (rewrite in "_\<^emph>(\<hole>) \<turnstile>_" graph_inv_def)
  apply iExistsL
  apply (iDestruct rule: graph_open[OF assms]) subgoal for G u m
  apply (iApply rule: wp_load[simplified, where ?l = x])
  apply iPureL+
  apply (iApply_step "heap_owns ?g ?m \<^emph> (m \<mapsto>\<^sub>u ?v1) \<^emph> (x \<mapsto>\<^sub>u ?v2)" rule: graph_close[of x])
  apply (iFrame3 "heap_owns ?g ?m", iExistsR u, iExistsR m, iFrame_single+)
  apply (iMod_wand "\<triangleright>?P" "heap_owns ?g ?m \<^emph> Own\<^sub>m ?m2 \<^emph> Own\<^sub>g ?g2")
  subgoal by (unfold graph_inv_def, entails_substR rule: upred_laterI, iExistsR G, iFrame_single+)
  apply (entails_substR rule: fupd_intro)
  apply (simp, rule wp_pure_let[OF pure_exec_fst, simplified], simp add: subst'_def)
  apply (entails_substR rule: wp_bind'[where C = Snd])
  apply (iMod rule: cinv_acc[OF subset_UNIV])
  apply (rewrite in "_\<^emph>(\<hole>) \<turnstile>_" graph_inv_def)
  apply iExistsL
  apply (iApply rule: graph_open[OF assms])
  apply iExistsL+ subgoal for G' u' m'
  apply iPureL+
  apply (iApply rule: upred_entails_trans[OF auth_own_graph_valid upred_entail_eqL[OF discrete_valid]])
  apply iPureL
  apply (cases u') subgoal for u1 u2 u3
  apply (cases u1)
  apply simp_all
  subgoal
    apply (iApply rule: wp_cmpxchg_fail[simplified, where ?l = m'], auto simp: vals_compare_safe_def)
    apply (entails_substR rule: wp_value)
    apply (iApply_step "heap_owns ?g ?m \<^emph> (m' \<mapsto>\<^sub>u TrueV) \<^emph> (x \<mapsto>\<^sub>u ?v)" rule: graph_close[of x])
    apply (iFrame3 "heap_owns ?g ?m", iExistsR u',iExistsR m', simp, iFrame_single+)
    apply (iMod rule: already_marked[of x]) using in_dom_of_graph apply (metis fmdom'_alt_def notin_fset)
    apply (iFrame3 "is_marked x")
    apply (iMod_wand "\<triangleright>?P" "heap_owns ?g ?m \<^emph> Own\<^sub>g ?g2 \<^emph> Own\<^sub>m ?m2")
    subgoal by (unfold graph_inv_def, entails_substR rule: upred_laterI, iExistsR G', (iFrame_single)+)
    apply (entails_substR rule: fupd_intro, rule wp_pure[OF pure_exec_snd, simplified])
    by (entails_substR rule: wp_value, simp, (iFrame_single)+)
  apply (iApply rule: wp_cmpxchg_success[simplified, where ?l = m'], auto simp: vals_compare_safe_def)
  apply (entails_substR rule: wp_value)
  apply (iMod rule: mark_graph[of _ x _ _ "(u2,u3)"])
  using in_dom_of_graph apply blast
  apply (iMod rule: new_marked)
  apply (iFrame3 "is_marked ?x \<^emph> cinv_own \<kappa> k")
  apply (subst drop_marked)
  apply (iDestruct rule: upred_entails_trans[OF auth_own_graph_valid upred_entail_eqL[OF discrete_valid]])
  apply (iApply_step "heap_owns ?g ?m \<^emph> (x\<mapsto>\<^sub>u?v1) \<^emph> (m'\<mapsto>\<^sub>u?v2)" rule: graph_close)
  apply (iFrame3 "heap_owns ?g ?m", iExistsR "(True,u2,u3)", iExistsR m, simp, (iFrame_single)+)
  apply iPureR using mark_update_lookup[OF assms] apply blast
  apply (iMod_wand "\<triangleright>?P" "heap_owns ?g ?m \<^emph> Own\<^sub>g ?g2 \<^emph> Own\<^sub>m ?m2")
  subgoal apply (entails_substR rule: upred_laterI, unfold graph_inv_def)
    apply (iExistsR "fmupd x(ex.Ex (u2, u3)) G'", iPureR)
    using mark_strict_subgraph[OF _ assms] apply blast by (simp add: op_fset_def, (iFrame_single)+)
  apply (entails_substR rule: fupd_intro, iApply rule: wp_pure[OF pure_exec_snd, simplified])
  apply (entails_substR rule: wp_value, simp, remove_emp)
  apply (iExistsR "(u2,u3)", iFrame_single)
  apply iPureR using of_graph_unmarked by simp
  done done done
end
end