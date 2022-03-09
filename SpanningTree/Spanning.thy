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
  unfolding try_mark_def
  apply (auto simp: subst'_def intro!: wp_pure[OF pure_exec_beta] wp_let_bind'[where C=Fst])
  unfolding graph_ctxt_def
  apply (iMod rule: cinv_acc[OF subset_UNIV])
  apply (rewrite in "_\<^emph>(\<hole>) \<turnstile>_" graph_inv_def)
  apply iExistsL
  apply (iApply rule: graph_open[OF assms])
  apply iExistsL+
  apply (iApply rule: wp_load[simplified, where ?l = x])
  apply iPureL+
  subgoal for G u m
  apply (iApply_step "heap_owns ?g ?m \<^emph> (m \<mapsto>\<^sub>u ?v1) \<^emph> (x \<mapsto>\<^sub>u ?v2)" rule: graph_close[of x])
  apply (move_sep_both "heap_owns ?g ?m")
  apply (rule upred_frame)
  apply (iExistsR u)
  apply (iExistsR m)
  apply iFrame_single+
  apply (simp only: upred_sep_assoc_eq)
  apply (iApply_step2 "\<triangleright>(graph_inv g Mrk)" "heap_owns ?g ?m \<^emph> Own\<^sub>m ?m2 \<^emph> Own\<^sub>g ?g2")
  subgoal unfolding graph_inv_def by (entails_substR rule: upred_laterI; iExistsR G; iFrame_single+)
  apply (simp add: upred_sep_assoc_eq)
  apply iApply_wand
  apply fupd_elimL
  apply (entails_substR rule: fupd_intro)
  apply (rule wp_pure_let[OF pure_exec_fst, simplified])
  apply (simp add: subst'_def)
  apply (entails_substR rule: wp_bind'[where C = Snd])
  apply (iMod rule: cinv_acc[OF subset_UNIV])
  apply (rewrite in "_\<^emph>(\<hole>) \<turnstile>_" graph_inv_def)
  apply iExistsL
  apply (iApply rule: graph_open[OF assms])
  apply iExistsL+
  apply iPureL+
  apply (iApply rule: upred_entails_trans[OF auth_own_graph_valid upred_entail_eqL[OF discrete_valid]])
  apply iPureL
  subgoal for G' u' m'
  apply (cases u')
  subgoal for u1 u2 u3
  apply (cases u1)
  subgoal
    apply simp
    apply (iApply rule: wp_cmpxchg_fail[simplified, where ?l = m'])
    apply (auto simp: vals_compare_safe_def)
    apply (entails_substR rule: wp_value)
    apply (iApply_step "heap_owns ?g ?m \<^emph> (m' \<mapsto>\<^sub>u TrueV) \<^emph> (x \<mapsto>\<^sub>u ?v)" rule: graph_close[of x])
    apply (move_sep_both "heap_owns ?g ?m")
    apply (rule upred_frame)
    apply (iExistsR u')
    apply (iExistsR m')
    apply simp apply iFrame_single+
    apply (unfold upred_sep_assoc_eq)
    apply (iMod rule: already_marked[of x])
    using in_dom_of_graph apply (metis fmdom'_alt_def notin_fset)
    apply (entails_substR rule: fupd_mono[OF wp_frame'])
    prefer 2 apply (split_pat "is_marked x")
    apply (entails_substR rule: fupd_frame_r)
    apply remove_emp
    apply (rule upred_frame)
    apply (iApply_step2 "\<triangleright>(graph_inv g Mrk)" "heap_owns ?g ?m \<^emph> Own\<^sub>g ?g2 \<^emph> Own\<^sub>m ?m2")
    subgoal unfolding graph_inv_def by (entails_substR rule: upred_laterI;iExistsR G';(iFrame_single)+)
    apply (simp only: upred_sep_assoc_eq) apply iApply_wand
    apply (rule fupd_frame_mono, simp only: upred_true_sep)
    apply (rule wp_pure[OF pure_exec_snd, simplified])
    apply (entails_substR rule: wp_value, simp)
    by (iFrame_single)+
  apply simp
  apply (move_sepL "m' \<mapsto>{?q}?v") apply (rule wp_cmpxchg_success[simplified])
  apply (auto simp: vals_compare_safe_def)
  apply (entails_substR rule: wp_value)
  apply (iMod rule: mark_graph[of _ x _ _ "(u2,u3)"])
  using in_dom_of_graph apply blast
  apply (iMod rule: new_marked)
  apply (entails_substR rule: fupd_mono[OF wp_frame'])
  prefer 2 apply (split_pat "is_marked x \<^emph> cinv_own \<kappa> k")
  apply (entails_substR rule: fupd_frame_r)
  apply remove_emp
  apply (iFrame_single) apply (rule upred_frame)
  apply (subst drop_marked)
  apply (iApply rule: upred_entails_trans[OF auth_own_graph_valid upred_entail_eqL[OF discrete_valid]])
  apply iPureL
  apply (iApply_step "heap_owns ?g ?m \<^emph> (x\<mapsto>\<^sub>u?v1) \<^emph> (m'\<mapsto>\<^sub>u?v2)" rule: graph_close)
  apply (move_sep_both "heap_owns ?g ?m")
  apply (rule upred_frame)
  apply (iExistsR "(True,u2,u3)")
  apply (iExistsR m)
  apply simp
  apply (iFrame_single)+
  apply iPureR
  using mark_update_lookup[OF assms] apply blast
  apply (simp only: upred_sep_assoc_eq)
  apply (iApply_step2 "\<triangleright>(graph_inv g Mrk)" "heap_owns ?g ?m \<^emph> Own\<^sub>g ?g2 \<^emph> Own\<^sub>m ?m2")
  subgoal unfolding graph_inv_def apply (entails_substR rule: upred_laterI)
    apply (iExistsR "fmupd x(ex.Ex (u2, u3)) G'")
    apply iPureR using mark_strict_subgraph[OF _ assms] apply blast
    apply (simp add: op_fset_def) by (iFrame_single)+
  apply (simp only: upred_sep_assoc_eq)
  apply iApply_wand
  apply (rule fupd_frame_mono)
  apply remove_emp
  apply (rule wp_pure[OF pure_exec_snd, simplified])
  apply (entails_substR rule: wp_value, simp)
  apply remove_emp
  apply (iExistsR "(u2,u3)")
  apply iFrame_single
  apply iPureR
  using of_graph_unmarked by simp
  done
  done
done
end
end