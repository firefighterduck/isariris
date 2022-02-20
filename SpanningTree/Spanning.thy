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
lemma wp_try_mark:
assumes "x\<in>dom g" 
shows "(graph_ctxt g Mrk) \<^emph> (own_graphUR q Map.empty) \<^emph> (cinv_own k) \<turnstile>
  WP (App (of_val try_mark) (of_val #[x])) 
  {{ \<lambda>v. 
    ((\<upharpoonleft>(v=#[True])) \<^emph> (\<exists>\<^sub>u u. (((\<upharpoonleft>(g x = Some u)) \<^emph> own_graphUR q (x [\<mapsto>\<^sub>g] u)) \<^emph> is_marked x \<^emph> cinv_own k)))
    \<or>\<^sub>u ((\<upharpoonleft>(v=#[False])) \<^emph> own_graphUR q Map.empty \<^emph> is_marked x \<^emph> cinv_own k) 
  }}"
sorry
end