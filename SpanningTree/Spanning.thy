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
  apply (subst (3) graph_inv_def)
  apply iExistsL
  apply (iDestruct rule: graph_open[OF assms]) subgoal for G u m
  apply (iApply rule: wp_load[simplified, where ?l = x])
  apply (iApply_step "heap_owns ?g ?m \<^emph> (m \<mapsto>\<^sub>u ?v1) \<^emph> (x \<mapsto>\<^sub>u ?v2)" rule: graph_close[of x])
  apply (iFrame2 "heap_owns ?g ?m")
  apply (iExistsR u, iExistsR m, iFrame_single+)
  apply (iMod_wand "\<triangleright>?P" "heap_owns ?g ?m \<^emph> Own\<^sub>m ?m2 \<^emph> Own\<^sub>g ?g2")
  subgoal by (unfold graph_inv_def, entails_substR rule: upred_laterI, iExistsR G, iFrame_single+)
  apply (entails_substR rule: fupd_intro)
  apply (simp, rule wp_pure_let[OF pure_exec_fst, simplified], simp add: subst'_def)
  apply (entails_substR rule: wp_bind'[where C = Snd])
  apply (iMod rule: cinv_acc[OF subset_UNIV])
  apply (subst (3) graph_inv_def)
  apply iExistsL
  apply (iDestruct rule: graph_open[OF assms]) subgoal for G' u' m'
  apply (iDestruct rule: upred_entails_trans[OF auth_own_graph_valid upred_entail_eqL[OF discrete_valid]])
  apply (cases u') subgoal for u1 u2 u3
  apply (cases u1)
  apply simp_all
  subgoal
    apply (iApply rule: wp_cmpxchg_fail[simplified, where ?l = m'], auto simp: vals_compare_safe_def)
    apply (entails_substR rule: wp_value)
    apply (iApply_step "heap_owns ?g ?m \<^emph> (m' \<mapsto>\<^sub>u TrueV) \<^emph> (x \<mapsto>\<^sub>u ?v)" rule: graph_close[of x])
    apply (iFrame2 "heap_owns ?g ?m", iExistsR u',iExistsR m', simp, iFrame_single+)
    apply (iMod rule: already_marked[of x]) using in_dom_of_graph apply (metis fmdom'_alt_def notin_fset)
    apply (iFrame2 "is_marked x")
    apply (iMod_wand "\<triangleright>?P" "heap_owns ?g ?m \<^emph> Own\<^sub>g ?g2 \<^emph> Own\<^sub>m ?m2")
    subgoal by (unfold graph_inv_def, entails_substR rule: upred_laterI, iExistsR G', (iFrame_single)+)
    apply (entails_substR rule: fupd_intro, rule wp_pure[OF pure_exec_snd, simplified])
    by (entails_substR rule: wp_value, simp, (iFrame_single)+)
  apply (iApply rule: wp_cmpxchg_success[simplified, where ?l = m'], auto simp: vals_compare_safe_def)
  apply (entails_substR rule: wp_value)
  apply (iMod rule: mark_graph[of _ x _ _ "(u2,u3)"])
  using in_dom_of_graph apply blast
  apply (iMod rule: new_marked)
  apply (iFrame2 "is_marked ?x \<^emph> cinv_own \<kappa> k")
  apply (subst drop_marked)
  apply (iDestruct rule: upred_entails_trans[OF auth_own_graph_valid upred_entail_eqL[OF discrete_valid]])
  apply (iApply_step "heap_owns ?g ?m \<^emph> (x\<mapsto>\<^sub>u?v1) \<^emph> (m'\<mapsto>\<^sub>u?v2)" rule: graph_close)
  apply (iFrame2 "heap_owns ?g ?m", iExistsR "(True,u2,u3)", iExistsR m', simp, (iFrame_single)+)
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

lemma wp_try_mark_isar:
assumes "x\<in>fmdom' g"
shows "(graph_ctxt \<kappa> g Mrk) \<^emph> (own_graphUR q fmempty) \<^emph> (cinv_own \<kappa> k) \<turnstile>
  WP (App (of_val try_mark) (of_val #[x])) 
  {{ \<lambda>v.
    ((\<upharpoonleft>(v=#[True])) \<^emph> (\<exists>\<^sub>u u. (((\<upharpoonleft>(fmlookup g x = Some u)) \<^emph> own_graphUR q (x [\<mapsto>\<^sub>g] u)))) \<^emph> is_marked x \<^emph> cinv_own \<kappa> k)
    \<or>\<^sub>u ((\<upharpoonleft>(v=#[False])) \<^emph> own_graphUR q fmempty \<^emph> is_marked x \<^emph> cinv_own \<kappa> k) 
  }}"
proof -
have later_graph_inv: "\<lbrakk>strict_subgraph' g (gmon_graph G); fmlookup (of_graph g G) x = Some u; Mrk x = Some m\<rbrakk> 
  \<Longrightarrow> heap_owns (of_graph g G) Mrk \<^emph> Own\<^sub>m full (fmdom G) \<^emph> Own\<^sub>g full (Some (G, 1)) \<turnstile> \<triangleright>graph_inv g Mrk"
  for G m u by (unfold graph_inv_def, entails_substR rule: upred_laterI, iExistsR G, iFrame_single+)
have try_mark_to_CAS:
  "Q \<^emph> graph_ctxt \<kappa> g Mrk \<^emph> cinv_own \<kappa> k \<turnstile> WP (App (of_val try_mark) (of_val #[x])) {{ P }}"
  if cas: "(\<And>m G u. \<lbrakk>strict_subgraph' g (gmon_graph G); fmlookup (of_graph g G) x = Some u; Mrk x = Some m\<rbrakk> \<Longrightarrow>
  Q \<^emph> cinv graphN \<kappa> (graph_inv g Mrk) \<^emph> cinv_own \<kappa> k \<turnstile> WP CAS (of_val (LitV (LitLoc m))) FalseE TrueE {{ P }})"
  for P Q
  apply (auto simp: try_mark_def subst'_def intro!: wp_pure[OF pure_exec_beta] wp_let_bind'[where C=Fst])
  apply (unfold graph_ctxt_def, iMod rule: cinv_acc[OF subset_UNIV], subst (3) graph_inv_def)
  apply (iExistsL, iDestruct rule: graph_open[OF assms]) subgoal for G u m
  apply (iApply rule: wp_load[simplified, where ?l = x])
  apply (iApply_step "heap_owns ?g ?m \<^emph> (m \<mapsto>\<^sub>u ?v1) \<^emph> (x \<mapsto>\<^sub>u ?v2)" rule: graph_close[of x])
  apply (iFrame2 "heap_owns ?g ?m", iExistsR u, iExistsR m, iFrame_single+)
  apply (iApply rule: later_graph_inv, auto, iApply_wand)
  apply (entails_substR rule: fupd_frame_mono, remove_emp)
  apply (rule wp_pure_let[OF pure_exec_fst, simplified], simp add: subst'_def) by (rule cas, auto) done
have split_cas: "\<lbrakk>fmlookup (of_graph g G) x = Some u; Mrk x = Some m\<rbrakk> \<Longrightarrow>
  P \<^emph> cinv graphN \<kappa> (graph_inv g Mrk) \<^emph> cinv_own \<kappa> k \<turnstile> WP CAS (of_val (LitV (LitLoc m))) FalseE TrueE {{ Q }}"
  if cmpxchgs: 
    "\<And>G' y z  E1 E2. \<lbrakk>strict_subgraph' g (gmon_graph G'); fmlookup (of_graph g G') x = Some (True, y, z); valid G'\<rbrakk> \<Longrightarrow>
    P \<^emph> cinv_own \<kappa> k \<^emph> ((\<triangleright>graph_inv g Mrk)={E1,E2}=\<^emph>upred_emp) \<^emph> heap_owns (fmdrop x (of_graph g G')) Mrk \<^emph> 
    Own\<^sub>m full (fmdom G') \<^emph> Own\<^sub>g full (Some (G', 1)) \<^emph> (x \<mapsto>\<^sub>u #[(m,children_to_val (y,z))]) \<^emph> (m\<mapsto>\<^sub>uTrueV) 
    \<turnstile> wp NotStuck E1 (of_val (PairV TrueV FalseV)) (\<lambda>v. \<Turnstile>{E1,E2}=> WP (Snd (of_val v)) {{ Q }})"
    "\<And>G' y z L E1 E2. \<lbrakk>strict_subgraph' g (gmon_graph G'); fmlookup (of_graph g G') x = Some (False, y, z); valid G'\<rbrakk> \<Longrightarrow>
    P \<^emph> cinv_own \<kappa> k \<^emph> ((\<triangleright>graph_inv g Mrk)={E1,E2}=\<^emph>upred_emp) \<^emph> heap_owns (fmdrop x (of_graph g G')) Mrk \<^emph> 
    Own\<^sub>m full (fmdom G') \<^emph> Own\<^sub>g full (Some (G', 1)) \<^emph> (x \<mapsto>\<^sub>u #[(m,children_to_val (y,z))]) \<^emph> (m\<mapsto>\<^sub>uTrueV)
    \<turnstile> wp NotStuck E1 (of_val (PairV FalseV TrueV)) (\<lambda>v. \<Turnstile>{E1,E2}=> WP (Snd (of_val v)) {{ Q }})"
  for P Q m G u
  apply (entails_substR rule: wp_bind'[where C = Snd],iMod rule: cinv_acc[OF subset_UNIV])
  apply (subst (3) graph_inv_def, iExistsL, iDestruct rule: graph_open[OF assms]) subgoal for G' u' m'
  apply (iDestruct rule: upred_entails_trans[OF auth_own_graph_valid upred_entail_eqL[OF discrete_valid]])
  apply (cases u') subgoal for u1 u2 u3 apply (cases u1) apply simp_all
  subgoal apply (iApply rule: wp_cmpxchg_fail[simplified, where ?l = m'], auto simp: vals_compare_safe_def)
  apply (move_sep_all True "P\<^emph>(cinv_own ?c ?d)\<^emph>(?l={?E1,?E2}=\<^emph>?e)\<^emph>heap_owns ?a ?b\<^emph>Own\<^sub>m full ?gm\<^emph>Own\<^sub>g full ?G\<^emph>(x\<mapsto>\<^sub>u?x)\<^emph>(m'\<mapsto>\<^sub>u?v)")
  using upred_extend[OF cmpxchgs(1), unfolded upred_sep_assoc_eq, simplified] by simp
  apply (iApply rule: wp_cmpxchg_success[simplified, where ?l = m'], auto simp: vals_compare_safe_def)
  apply (move_sep_all True "P\<^emph>(cinv_own ?c ?d)\<^emph>(?l={?E1,?E2}=\<^emph>?e)\<^emph>heap_owns ?a ?b\<^emph>Own\<^sub>m full ?gm\<^emph>Own\<^sub>g full ?G\<^emph>(x\<mapsto>\<^sub>u?x)\<^emph>(m'\<mapsto>\<^sub>u?v)")
  using upred_extend[OF cmpxchgs(2), unfolded upred_sep_assoc_eq] by simp done done
have later_graph_inv2: "\<lbrakk>fmlookup (of_graph g G) x = Some (False, y, z); strict_subgraph' g (gmon_graph G); 
  valid (fmupd x (Ex (y, z)) G)\<rbrakk> \<Longrightarrow>
  heap_owns (of_graph g (fmupd x (Ex (y, z)) G)) Mrk \<^emph> Own\<^sub>m full (fmdom G \<cdot> {|x|}) \<^emph> 
  Own\<^sub>g full (Some (fmupd x (Ex (y, z)) G, 1)) 
  \<turnstile> \<triangleright>graph_inv g Mrk" for G y z
  apply (entails_substR rule: upred_laterI, unfold graph_inv_def,iExistsR "fmupd x(ex.Ex (y, z)) G", iPureR)
  using mark_strict_subgraph[OF _ assms] apply blast by (simp add: op_fset_def, (iFrame_single)+)
have last: "fmlookup (of_graph g G) x = Some (False, (y,z)) \<Longrightarrow>
  P (y,z) \<turnstile> WP TrueE {{ \<lambda>xa. ((\<exists>\<^sub>uu. \<upharpoonleft>fmlookup g x = Some u \<^emph> P u) \<^emph> \<upharpoonleft>xa = TrueV) \<or>\<^sub>u (Q \<^emph> \<upharpoonleft>xa = FalseV) }}"
for P Q y z G
  apply (entails_substR rule: wp_value, simp, remove_emp) apply (iExistsR "(y,z)", iFrame_single)
  apply iPureR using of_graph_unmarked by simp
have cmpxchg_suc: "\<lbrakk>strict_subgraph' g (gmon_graph G'); fmlookup (of_graph g G') x = Some (False, y, z);
  Mrk x = Some m;valid G'\<rbrakk> \<Longrightarrow>
  own_graphUR q fmempty \<^emph> cinv_own \<kappa> k \<^emph> ((\<triangleright>graph_inv g Mrk)={E1,E2}=\<^emph>upred_emp) \<^emph> heap_owns (fmdrop x (of_graph g G')) Mrk \<^emph> 
  (Own\<^sub>m (full (fmdom G'))) \<^emph> (Own\<^sub>g (full (Some (G', 1)))) \<^emph> 
  (x \<mapsto>\<^sub>u PairV (LitV (LitLoc m)) (children_to_val (y, z))) \<^emph> (m \<mapsto>\<^sub>u TrueV)
  \<turnstile> wp NotStuck E1 (of_val (PairV FalseV TrueV)) (\<lambda>v. \<Turnstile>{E1,E2}=>WP Snd (of_val v) {{ \<lambda>v.
    ((\<upharpoonleft>(v=TrueV)) \<^emph> (\<exists>\<^sub>u u. (((\<upharpoonleft>(fmlookup g x = Some u)) \<^emph> own_graphUR q (x [\<mapsto>\<^sub>g] u)))) \<^emph> is_marked x \<^emph> cinv_own \<kappa> k)
    \<or>\<^sub>u ((\<upharpoonleft>(v=FalseV)) \<^emph> own_graphUR q fmempty \<^emph> is_marked x \<^emph> cinv_own \<kappa> k) 
  }})" 
  for m y z G' E1 E2
  apply (entails_substR rule: wp_value, iMod rule: mark_graph[of _ x _ _ "(y,z)"])
  using in_dom_of_graph apply blast apply (iMod rule: new_marked)
  apply (iFrame2 "is_marked ?x \<^emph> cinv_own \<kappa> k", subst drop_marked)
  apply (iDestruct rule: upred_entails_trans[OF auth_own_graph_valid upred_entail_eqL[OF discrete_valid]])
  apply (iApply_step "heap_owns ?g ?m \<^emph> (x\<mapsto>\<^sub>u?v1) \<^emph> (m\<mapsto>\<^sub>u?v2)" rule: graph_close)
  apply (iFrame2 "heap_owns ?g ?m", iExistsR "(True,y,z)", iExistsR m, simp, (iFrame_single)+)
  apply iPureR using mark_update_lookup[OF assms] apply blast
  apply (iMod_wand "\<triangleright>?P" "heap_owns ?g ?m \<^emph> Own\<^sub>g ?g2 \<^emph> Own\<^sub>m ?m2", rule later_graph_inv2, auto)
  apply (entails_substR rule: fupd_intro, iApply rule: wp_pure[OF pure_exec_snd, simplified])
  using last[where P1 = "\<lambda>u. own_graphUR q (x [\<mapsto>\<^sub>g] u)"] by (simp add: upred_sep_comm)
have cmpxchg_fail: "\<lbrakk>strict_subgraph' g (gmon_graph G'); fmlookup (of_graph g G') x = Some (True, y, z);
  Mrk x = Some m;valid G'\<rbrakk> \<Longrightarrow>
  own_graphUR q fmempty \<^emph> cinv_own \<kappa> k \<^emph> ((\<triangleright>graph_inv g Mrk)={E1,E2}=\<^emph>upred_emp) \<^emph> heap_owns (fmdrop x (of_graph g G')) Mrk \<^emph> 
  (Own\<^sub>m (full (fmdom G'))) \<^emph> (Own\<^sub>g (full (Some (G', 1)))) \<^emph> 
  (x \<mapsto>\<^sub>u PairV (LitV (LitLoc m)) (children_to_val (y, z))) \<^emph> (m \<mapsto>\<^sub>u TrueV)
  \<turnstile> wp NotStuck E1 (of_val (PairV TrueV FalseV)) (\<lambda>v. \<Turnstile>{E1,E2}=>WP Snd (of_val v) {{ \<lambda>v.
    ((\<upharpoonleft>(v=TrueV)) \<^emph> (\<exists>\<^sub>u u. (((\<upharpoonleft>(fmlookup g x = Some u)) \<^emph> own_graphUR q (x [\<mapsto>\<^sub>g] u)))) \<^emph> is_marked x \<^emph> cinv_own \<kappa> k)
    \<or>\<^sub>u ((\<upharpoonleft>(v=FalseV)) \<^emph> own_graphUR q fmempty \<^emph> is_marked x \<^emph> cinv_own \<kappa> k) 
  }})" 
  for m y z G' E1 E2
  apply (entails_substR rule: wp_value)
  apply (iApply_step "heap_owns ?g ?m \<^emph> (m \<mapsto>\<^sub>u TrueV) \<^emph> (x \<mapsto>\<^sub>u ?v)" rule: graph_close[of x])
  apply (iFrame2 "heap_owns ?g ?m", iExistsR "(True,y,z)",iExistsR m, simp, iFrame_single+)
  apply (iMod rule: already_marked[of x]) using in_dom_of_graph apply (metis fmdom'_alt_def notin_fset)
  apply (iFrame2 "is_marked x",iApply rule: later_graph_inv, auto, iApply_wand)
  apply (entails_substR rule: fupd_frame_mono, rule wp_pure[OF pure_exec_snd, simplified])
  by (entails_substR rule: wp_value, simp, (iFrame_single)+)
show ?thesis apply (iApply rule: try_mark_to_CAS) apply (iDrop "graph_ctxt ?x ?y ?z")+
  by (auto intro!: split_cas cmpxchg_suc cmpxchg_fail)
qed
end
end