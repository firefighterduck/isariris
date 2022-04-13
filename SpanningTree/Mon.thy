theory Mon
imports SpanningTreeCameras
  "../IrisCore/Invariant"
  "../HeapLang/Notation"
  "../IrisCore/Misc"
  "../IrisCore/AuthHeap"
   "HOL-Library.Rewrite"
begin

subsection \<open> The underlying structures of the spanning tree \<close>
text \<open> Based on \<^url>\<open>https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/spanning_tree/mon.v\<close> \<close>

definition "graph_name :: gname \<equiv> 5"
definition "marking_name :: gname \<equiv> 6"

definition graphN :: namespace where "graphN = add_name nroot (string_to_name ''SPT_graph'')"
abbreviation own_graph :: "graphUR auth \<Rightarrow> iprop" ("Own\<^sub>g _" 85) where
  "own_graph g \<equiv> Own(constr_graph graph_name g)"
abbreviation own_marking :: "markingUR auth \<Rightarrow> iprop" ("Own\<^sub>m _" 85) where
  "own_marking m \<equiv> Own(constr_markings marking_name m)"

lemma n_incl_fragm_l: "n_incl n (fragm {l}) a = (case a of Auth (b,c) \<Rightarrow> l\<in>c)"
  by (auto split: auth.splits)

text \<open> Marking Definitions \<close>
definition is_marked ::"loc \<Rightarrow> iprop" where "is_marked l = Own\<^sub>m(fragm {|l|})"

lemma is_marked_split: "Own\<^sub>m(fragm {|l|}) = Own\<^sub>m(fragm {|l|} \<cdot> fragm {|l|})"
  by (auto simp: auth_frag_op[symmetric] op_fset_def)

lemma dup_marked: "is_marked l \<stileturn>\<turnstile> is_marked l \<^emph> is_marked l"
proof -
from upred_own_op have "Own (constr_markings marking_name (fragm {|l|}) \<cdot> 
  constr_markings marking_name (fragm {|l|})) \<stileturn>\<turnstile> (Own\<^sub>m(fragm {|l|})) \<^emph> Own\<^sub>m(fragm {|l|})" 
  by auto
then have "Own(constr_markings marking_name (fragm {|l|}\<cdot>fragm {|l|})) \<stileturn>\<turnstile> Own\<^sub>m(fragm {|l|}) \<^emph> Own\<^sub>m(fragm {|l|})" 
  by (auto simp add: op_prod_def \<epsilon>_left_id constr_markings_def)
then show ?thesis unfolding is_marked_split[symmetric] by (simp add: is_marked_def)
qed

type_synonym gmon = "(loc,(chl ex)) fmap"

fun excl_chlC_chl :: "chl ex \<Rightarrow> chl option" where
  "excl_chlC_chl (Ex w) = Some w"
| "excl_chlC_chl ex.Inv = None"

context includes fmap.lifting begin
lift_definition gmon_graph :: "gmon \<Rightarrow> loc graph_map" is
  "\<lambda>g. (\<lambda>l. Option.bind l excl_chlC_chl) \<circ> g" .
end

lemma gmon_graph_dom: "valid g \<Longrightarrow> (dom (gmon_graph g) = fmdom' g)"
proof -
  assume assm: "valid g"
  then have "\<forall>i. valid (fmlookup g i)" 
    by (auto simp: valid_def valid_raw_fmap_def valid_raw_fun.rep_eq)
  then have "\<forall>j\<in>fmran' g. valid j" 
    by (auto simp: fmran'_def valid_def valid_raw_option_def split: option.splits)
  then have "\<forall>j\<in>fmran' g. j \<noteq> ex.Inv" by (auto simp: valid_def valid_raw_ex_def)
  then have "\<forall>j\<in>fmran' g. \<exists>j'. j= Ex j' \<and> excl_chlC_chl j = Some j'" by (meson excl_chlC_chl.elims)
  then have "\<forall>i\<in>fmdom' g. \<exists>j'. fmlookup g i = Some (Ex j') \<and> excl_chlC_chl (the (fmlookup g i)) = Some j'"
    apply auto by (metis fmlookup_dom'_iff fmran'I option.sel)
  then have "\<forall>i\<in>fmdom' g. \<exists>j'. ((\<lambda>l. Option.bind l excl_chlC_chl) \<circ> fmlookup g) i = Some j'"
    by auto
  then have rtol: "fmdom' g \<subseteq> dom (gmon_graph g)" by (auto simp: gmon_graph.rep_eq)
  have "\<nexists>j'. Option.bind None excl_chlC_chl = Some j'" by auto
  then have "\<forall>i\<in> -fmdom' g. \<nexists>j'. ((\<lambda>l. Option.bind l excl_chlC_chl) \<circ> fmlookup g) i = Some j'"
    by auto
  then have "dom (gmon_graph g) \<subseteq> fmdom' g" apply (auto simp: gmon_graph.rep_eq) by blast  
  with rtol show ?thesis by auto
qed

fun child_to_val :: "loc option \<Rightarrow> val" where
  "child_to_val None = NoneV"
| "child_to_val (Some l) = SomeV (LitV (LitLoc l))"

definition children_to_val :: "chl \<Rightarrow> val" where
  "children_to_val chs = PairV (child_to_val (fst chs)) (child_to_val (snd chs))"

type_synonym marked_graph = "(loc,(bool\<times>chl)) fmap"

definition of_graph_elem :: "gmon \<Rightarrow> loc \<Rightarrow> chl \<Rightarrow> (bool\<times>chl)" where
  "of_graph_elem g l v = (case gmon_graph g l of Some w \<Rightarrow> (True,w) | None \<Rightarrow> (False, v))"

definition of_graph :: "loc graph \<Rightarrow> gmon \<Rightarrow> marked_graph" where
  "of_graph g G = fmmap_keys (\<lambda>l chl. of_graph_elem G l chl) g"

lemma of_graph_dom: "fmdom' (of_graph g G) = fmdom' g"
  unfolding of_graph_def of_graph_elem_def fmdom'_alt_def fmdom_fmmap_keys
  by auto 

definition own_graphUR :: "frac \<Rightarrow> gmon \<Rightarrow> iprop" where
  "own_graphUR q G = Own\<^sub>g(fragm (Some (G,q)))"

definition heap_owns :: "marked_graph \<Rightarrow> (loc\<rightharpoonup>loc) \<Rightarrow> iprop" where
  "heap_owns M markings = 
  sep_map_fset (\<lambda>(l,(b,cl)). (\<exists>\<^sub>u m. ((\<upharpoonleft>(markings l = Some m))
    \<^emph> (l\<mapsto>\<^sub>u#[(m, children_to_val cl)])
    \<^emph> (m\<mapsto>\<^sub>u#[b]))))
  (fset_of_fmap M)"

definition graph_inv :: "loc graph \<Rightarrow> (loc\<rightharpoonup>loc) \<Rightarrow> iprop" where
  "graph_inv g markings \<equiv> \<exists>\<^sub>u (G::gmon). ((Own\<^sub>g(full (Some (G, 1))))
    \<^emph> (Own\<^sub>m(full (fmdom G))) \<^emph> (heap_owns (of_graph g G) markings) 
    \<^emph> (\<upharpoonleft>(strict_subgraph' g (gmon_graph G))))"

lemma own_graph_timeless [timeless_rule,log_prog_rule]:"timeless (Own\<^sub>g g)"
  unfolding timeless_def except_zero_def constr_graph_def
  by transfer (auto simp: singleton_map_n_incl d_equiv)

lemma own_markings_timeless [timeless_rule,log_prog_rule]:"timeless (Own\<^sub>m m)"
  unfolding timeless_def except_zero_def constr_markings_def
  by transfer (auto simp: singleton_map_n_incl d_equiv)

lemma graph_inv_timeless [timeless_rule,log_prog_rule]: "timeless (graph_inv g m)"
  unfolding graph_inv_def heap_owns_def
  apply timeless_solver
  apply auto by timeless_solver

definition graph_ctxt :: "gname \<Rightarrow> loc graph \<Rightarrow> (loc\<rightharpoonup>loc) \<Rightarrow> iprop" where 
  "graph_ctxt \<kappa> g Mrk \<equiv> cinv graphN \<kappa> (graph_inv g Mrk)"

lemma graph_ctxt_persistent [pers_rule,log_prog_rule]: "persistent (graph_ctxt \<kappa> g Mrk)"
  unfolding graph_ctxt_def by (rule cinv_persistent)

abbreviation gmon_map :: "loc \<Rightarrow> chl \<Rightarrow> gmon" where "gmon_map l v \<equiv> fmupd l (Ex v) fmempty"
notation gmon_map (infix "[\<mapsto>\<^sub>g]" 60)

lemma graph_open: "x \<in> fmdom' g \<Longrightarrow>
  (Own\<^sub>g (full (Some (G,1)))) \<^emph> heap_owns (of_graph g G) markings \<turnstile>
  (Own\<^sub>g (full (Some (G,1)))) \<^emph> heap_owns (fmdrop x (of_graph g G)) markings 
  \<^emph> (\<exists>\<^sub>u u. (\<upharpoonleft>(fmlookup (of_graph g G) x = Some u)) \<^emph> (\<exists>\<^sub>u m. (\<upharpoonleft>(markings x = Some m)) 
    \<^emph> (x \<mapsto>\<^sub>u #[(m, children_to_val (snd u))]) \<^emph> (m \<mapsto>\<^sub>u #[fst u])))"
proof -
  assume "x \<in> fmdom' g"
  then have "x \<in> fmdom' (of_graph g G)" by (simp add: of_graph_dom)
  then have "\<exists>y. fmlookup (of_graph g G) x = Some y" by (simp add: fmlookup_dom'_iff)
  then obtain y where y: "fmlookup (of_graph g G) x = Some y" by auto
  then have "(of_graph g G) = fmupd x y (of_graph g G)" by (metis fmap_ext fmupd_lookup)
  then have rw: "(of_graph g G) = fmupd x y (fmdrop x (of_graph g G))"
    by (smt (verit, ccfv_threshold) fmap_ext fmlookup_drop fmupd_lookup) 
  have "fmlookup (fmdrop x (of_graph g G)) x = None" by simp
  show ?thesis
    unfolding heap_owns_def y
    apply (rewrite in "(_ \<^emph> [\<^emph>\<^sub>m] _ (_ \<hole>)) \<turnstile> _" rw)
    apply (rule upred_entails_substE[OF upred_entail_eqL[OF sep_map_fset_insert[OF 
        \<open>fmlookup (fmdrop x (of_graph g G)) x = None\<close>]], unfolded upred_sep_assoc_eq])
    apply (move_sepR "[\<^emph>\<^sub>m] ?P ?m")
    apply (auto simp: intro!: upred_sep_mono upred_existsI[of _ _ y] split: prod.splits)
    apply (entails_substR rule: upred_sep_comm)
    by (auto simp: upred_true_sep)
qed

lemma graph_close: 
  "heap_owns (fmdrop x (of_graph g G)) markings \<^emph> 
  (\<exists>\<^sub>u u. (\<upharpoonleft>(fmlookup (of_graph g G) x = Some u)) \<^emph> (\<exists>\<^sub>u m. (\<upharpoonleft>(markings x = Some m)) 
    \<^emph> (x \<mapsto>\<^sub>u #[(m, children_to_val (snd u))]) \<^emph> (m \<mapsto>\<^sub>u #[fst u])))
  \<turnstile> heap_owns (of_graph g G) markings"
proof -
  have upd_drop: "fmlookup (of_graph g G) x = Some u \<Longrightarrow> (of_graph g G) = fmupd x u (fmdrop x (of_graph g G))" 
    for u by (smt (verit, best) fmap_ext fmlookup_drop fmupd_lookup)
  have lookup_drop: "fmlookup (fmdrop x (of_graph g G)) x = None" by simp
  show ?thesis 
  apply iExistsL+
  apply iPureL+
  subgoal for u m
  apply (rewrite in "_\<turnstile>\<hole>" heap_owns_def)
  apply (rewrite in "_\<turnstile> [\<^emph>\<^sub>m] _ (_ \<hole>)" upd_drop, assumption)
  unfolding heap_owns_def
  apply (entails_substR rule: upred_entail_eqR[OF sep_map_fset_insert[OF lookup_drop]])
  apply (auto simp: upred_sep_assoc_eq split: prod.splits)
  apply (entails_substL rule: upred_sep_comm2L)
  apply (move_sepL "[\<^emph>\<^sub>m] ?P ?m")
  apply (iFrame_single)
  by (iExistsR m)
  done
qed

lemma auth_own_graph_valid: "Own\<^sub>g (full (Some (G,q))) \<turnstile> \<V> G"
apply (auto simp: constr_graph_def)
apply (entails_substL rule: upred_own_valid)
apply transfer'
by (auto simp: \<epsilon>_n_valid prod_n_valid_def valid_raw_option_def)

lemma new_marked: "(Own\<^sub>m (full m)) ={E}=\<^emph> (Own\<^sub>m (full (m\<cdot>{|l|})) \<^emph> is_marked l)"
apply iIntro
unfolding is_marked_def constr_markings_def
apply (entails_substR rule: fupd_mono[OF upred_entail_eqL[OF upred_own_op]])
apply (rule upred_entails_trans[OF upred_wand_holdsE[OF upred_own_update] upred_wand_holdsE[OF upd_fupd]])
apply (auto simp: camera_upd_def prod_n_valid_def op_prod_def \<epsilon>_left_id)
sorry

lemma already_marked: "l |\<in>| m \<Longrightarrow>
  (Own\<^sub>m (full m)) ={E}=\<^emph> (Own\<^sub>m (full m) \<^emph> is_marked l)"
  apply iIntro
  apply (entails_substL rule: new_marked)
  apply (rule fupd_mono)
  apply (rule upred_frame)
  sorry

lemma in_dom_of_graph: "\<lbrakk>valid G; fmlookup (of_graph g G) x = Some (b,v)\<rbrakk> \<Longrightarrow> b \<longleftrightarrow> x \<in> fmdom' G"
proof -
  assume assms: "valid G" "fmlookup (of_graph g G) x = Some (b,v)"
  from assms(2) have "fmlookup (fmmap_keys (\<lambda>l chl. of_graph_elem G l chl) g) x = Some (b,v)" 
    unfolding of_graph_def .
  with fmlookup_fmmap_keys have step1: "map_option (\<lambda>chl. of_graph_elem G x chl) (fmlookup g x) = Some (b,v)"
    by simp
  then obtain v' where "fmlookup g x = Some v'" by blast
  with step1 have "of_graph_elem G x v' = (b,v)" by simp
  then have "(case gmon_graph G x of Some w \<Rightarrow> (True,w) | None \<Rightarrow> (False, v')) = (b,v)"
    unfolding of_graph_elem_def .
  then have "b \<longleftrightarrow> x \<in> dom (gmon_graph G)"
    by (metis (no_types, lifting) Pair_inject domD domIff option.simps(4) option.simps(5))
  with gmon_graph_dom[OF assms(1)] show ?thesis by simp
qed

lemma mark_graph: "fmlookup G x = None \<Longrightarrow>
  ((Own\<^sub>g (full (Some (G,1)))) \<^emph> own_graphUR q fmempty) ={E}=\<^emph>
  ((Own\<^sub>g (full (Some (fmupd x (Ex w) G, 1)))) \<^emph> (own_graphUR q (x [\<mapsto>\<^sub>g] w)))"
  sorry

lemma drop_marked: "fmdrop x (of_graph g G) = fmdrop x (of_graph g (fmupd x (Ex w) G))"
proof -
have not_x_gmon_graph: "\<forall>y. x\<noteq>y \<longrightarrow> gmon_graph G y = gmon_graph (fmupd x (Ex w) G) y"
  by (auto simp: gmon_graph_def)
have "fmdrop x (of_graph g G) = fmdrop x (fmmap_keys (\<lambda>l chl. of_graph_elem G l chl) g)" 
  unfolding of_graph_def ..
also have "\<dots> = fmmap_keys (\<lambda>l chl. of_graph_elem G l chl) (fmdrop x g)" by simp
also have "\<dots> = fmmap_keys (\<lambda>l chl. (case gmon_graph G l of Some w \<Rightarrow> (True,w) | None \<Rightarrow> (False, chl)))
  (fmdrop x g)" unfolding of_graph_elem_def ..
also have "\<dots> = fmmap_keys (\<lambda>l chl. (case gmon_graph (fmupd x (Ex w) G) l of Some w \<Rightarrow> (True,w) 
  | None \<Rightarrow> (False, chl))) (fmdrop x g)" using not_x_gmon_graph by (simp add: fmap_ext)
finally have "fmdrop x (of_graph g G) = fmdrop x (of_graph g (fmupd x (Ex w) G))" unfolding of_graph_elem_def of_graph_def
  by simp
then show ?thesis .
qed

lemma mark_update_lookup: "\<lbrakk>x \<in> fmdom' g; valid (fmupd x (Ex v) G)\<rbrakk> \<Longrightarrow> 
  fmlookup (of_graph g (fmupd x (Ex v) G)) x = Some (True, v)" 
  unfolding valid_def of_graph_def fmlookup_fmmap_keys of_graph_elem_def gmon_graph_def
  by (auto simp: fmlookup_dom'_iff)

lemma mark_strict_subgraph: 
  "\<lbrakk>valid (fmupd x (Ex v) G); x \<in> fmdom' g; fmlookup (of_graph g G) x = Some (false, v);
  strict_subgraph' g (gmon_graph G)\<rbrakk> \<Longrightarrow> strict_subgraph' g (gmon_graph (fmupd x (Ex v) G))"
  apply (auto simp: valid_def strict_subgraph'_def of_graph_def of_graph_elem_def strict_sub_children_def)
  sorry

lemma of_graph_unmarked: "fmlookup (of_graph g G) x = Some (False, v) \<Longrightarrow> fmlookup g x = Some v"
  by (auto simp: of_graph_def of_graph_elem_def) (metis Pair_inject option.case_eq_if)

end