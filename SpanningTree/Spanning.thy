theory Spanning
imports Mon "../HeapLang/Par" "../HeapLang/WeakestPrecondition" "HOL-Library.Rewrite"
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
    ((\<upharpoonleft>(v=#[True])) \<^emph> (\<exists>\<^sub>u u. (((\<upharpoonleft>(fmlookup g x = Some u)) \<^emph> own_graphUR q (x [\<mapsto>\<^sub>g] u)) \<^emph> is_marked x \<^emph> cinv_own \<kappa> k)))
    \<or>\<^sub>u ((\<upharpoonleft>(v=#[False])) \<^emph> own_graphUR q fmempty \<^emph> is_marked x \<^emph> cinv_own \<kappa> k) 
  }}"
  unfolding try_mark_def
  apply (auto simp: subst'_def intro!: wp_pure[OF pure_exec_beta] wp_let_bind'[where C=Fst])
  unfolding graph_ctxt_def
  apply (move_sepL "cinv ?N ?\<kappa> ?P")
  apply dupl_pers
  apply (move_sepL "cinv_own ?N ?\<kappa>")
  apply (entails_substL rule: upred_wand_holds2E[OF cinv_acc])
  apply (rule subset_UNIV)
  apply (auto simp: upred_sep_assoc_eq intro!: elim_modal_entails'[OF elim_modal_fupd_wp_atomic[OF atomic_load]])
  apply (move_sepL "\<triangleright>(graph_inv g Mrk)")
  apply (rule elim_modal_entails'[OF elim_modal_timeless[OF graph_inv_timeless[unfolded timeless_def] wp_is_except_zero]])
  apply (rewrite in "_\<^emph>(\<hole>) \<turnstile>_" graph_inv_def)
  apply (auto simp: upred_sep_assoc_eq intro!: pull_exists_antecedentR upred_existsE')
  sorry
end
end