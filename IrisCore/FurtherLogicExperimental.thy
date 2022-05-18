theory FurtherLogicExperimental
imports DerivedConstructions Frac BaseLogicDeepExperimental2 Namespace "../HeapLang/PrimitiveLaws"
  "../SpanningTree/SpanningTreeCameras" "../HeapLang/State"
begin

datatype inv = Inv "(name, iprop later) map_view \<times> name dset \<times> name dfset"
  and iprop = iProp (pred: "(graphUR auth \<times> markingUR auth \<times> inv \<times> heap_lang_heap) cmra_pred")

instance inv :: ucamera sorry
instance iprop :: ofe sorry

declare [[coercion pred, coercion Inv]]
  
abbreviation own_heap :: "heap_lang_heap \<Rightarrow> iprop" ("Own\<^sub>h _") where
  "own_heap h \<equiv> iProp (Atom (Own (ConstC (\<epsilon>,\<epsilon>,\<epsilon>,h))))"

definition points_to :: "loc \<Rightarrow> dfrac \<Rightarrow> val \<Rightarrow> iprop" where
  "points_to l dq v = Own\<^sub>h(view_frag [l\<mapsto>(dq, to_ag (Some v))])"
abbreviation points_to_disc :: "loc \<Rightarrow> val \<Rightarrow> iprop" where 
  "points_to_disc \<equiv> \<lambda>l v. points_to l DfracDiscarded v"
abbreviation points_to_own :: "loc \<Rightarrow> frac \<Rightarrow> val \<Rightarrow> iprop" where
  "points_to_own \<equiv> \<lambda>l p v. points_to l (DfracOwn p) v"
abbreviation points_to_full :: "loc \<Rightarrow> val \<Rightarrow> iprop" where
  "points_to_full \<equiv> \<lambda>l v. points_to_own l 1 v"

definition "iprop_holds iP \<equiv> case iP of iProp P \<Rightarrow> pred_holds P"
  
lemma points_to_valid: 
  "iprop_holds (iProp (Wand (pred (points_to l dq v)) (Pure (valid dq))))"
  unfolding pred_holds_def upred_holds_def points_to_def iprop_holds_def
  apply auto
  sorry

definition own_inv :: "inv \<Rightarrow> iprop" ("Own\<^sub>i _") where
  "own_inv i = iProp (Atom (Own(ConstC (\<epsilon>,\<epsilon>,i,\<epsilon>))))"

definition own_state_heap :: "state \<Rightarrow> iprop" where
  "own_state_heap s = Own\<^sub>h (view_auth_full (heap s))"

definition sep_map_set :: "('b\<Rightarrow>iprop) \<Rightarrow> 'b set \<Rightarrow> iprop" where
  "sep_map_set f s = iProp (folding_on.F (\<lambda>x a. Sep a (pred (f x))) (Pure True) s)"
  
context assumes "SORT_CONSTRAINT('c::ucamera)" and "SORT_CONSTRAINT('v::ofe)"
begin

definition ownI :: "name \<Rightarrow> iprop \<Rightarrow> iprop" where
  "ownI \<iota> P = Own\<^sub>i (Inv (view_frag [\<iota>\<mapsto>(DfracDiscarded,to_ag (Next P))],\<epsilon>,\<epsilon>))"

definition inv :: "namespace \<Rightarrow> iprop \<Rightarrow> iprop" where
  "inv N P = iProp (\<exists>\<^sub>u \<iota>. (Conj (Pure (uname \<iota>\<in>names N)) (pred (ownI (uname \<iota>) P))))"
  
definition ownE :: "name dset \<Rightarrow> iprop" where
  "ownE E = Own\<^sub>i (Inv (\<epsilon>,E,\<epsilon>))"

definition ownD :: "name dfset \<Rightarrow> iprop" where
  "ownD D = Own\<^sub>i (Inv (\<epsilon>,\<epsilon>,D))"
  
definition lift_inv_fmap :: "(name,iprop) fmap \<Rightarrow> (name,iprop later) fmap" where
  "lift_inv_fmap m = Abs_fmap (map_option Next \<circ> (fmlookup m))"
  
definition wsat :: iprop where
  "wsat \<equiv> \<exists>\<^sub>u (I::(name,iprop) fmap).
    (Sep (pred (Own\<^sub>i (Inv(view_auth_full(lift_inv_fmap I),\<epsilon>,\<epsilon>))))
     (pred (sep_map_set (\<lambda>\<iota>. iProp (Disj (Sep (Later((pred \<circ> the \<circ> (fmlookup I)) \<iota>)) (pred (ownD (DFSet {|\<iota>|})))) 
      (pred (ownE (DSet {\<iota>}))))) (fmdom' I))))"
end
  
function wp :: "expr \<Rightarrow> (val \<Rightarrow> iprop) \<Rightarrow> iprop" where
  "wp e \<Phi> = iProp (case to_val e of Some v \<Rightarrow> BUpd (pred (\<Phi> v))
    | None \<Rightarrow> (\<forall>\<^sub>u \<sigma>. (Wand (pred (own_state_heap (ustate \<sigma>)))
      (BUpd (Conj (Pure(red e (ustate \<sigma>))) (Later (\<forall>\<^sub>u \<kappa> e2 \<sigma>2 efs. Wand 
      (Pure(e (ustate \<sigma>) (ulist uobs \<kappa>) \<Rightarrow>\<^sub>h (uexpr e2) (ustate \<sigma>2) (ulist uexpr efs)))
        (BUpd (Sep (pred (own_state_heap (ustate \<sigma>2))) 
        (Sep (pred (wp (uexpr e2) \<Phi>)) 
        (pred (sep_map_set (\<lambda>e'. (wp e' (\<lambda>_. iProp (Pure True)))) (set (ulist uexpr efs)
        )))))))))))))"
  by fast auto
  
end