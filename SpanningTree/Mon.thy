theory Mon
imports SpanningTreeCameras
  "../IrisCore/Invariant"
  "../HeapLang/Notation"
  "../IrisCore/Misc"
  "../IrisCore/AuthHeap"
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
from own_op have "Own (constr_markings marking_name (fragm {|l|}) \<cdot> 
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
thm gmon_graph.rep_eq
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

lemma own_graph_timeless [timeless_rule]:"timeless (Own\<^sub>g g)"
  unfolding timeless_def except_zero_def constr_graph_def
  by transfer (auto simp: singleton_map_n_incl d_equiv)

lemma own_markings_timeless [timeless_rule]:"timeless (Own\<^sub>m m)"
  unfolding timeless_def except_zero_def constr_markings_def
  by transfer (auto simp: singleton_map_n_incl d_equiv)

lemma graph_inv_timeless [timeless_rule]: "timeless (graph_inv g m)"
  unfolding graph_inv_def heap_owns_def
  apply timeless_solver
  apply auto by timeless_solver

definition graph_ctxt :: "gname \<Rightarrow> loc graph \<Rightarrow> (loc\<rightharpoonup>loc) \<Rightarrow> iprop" where 
  "graph_ctxt \<kappa> g Mrk \<equiv> cinv graphN \<kappa> (graph_inv g Mrk)"

lemma graph_ctxt_persistent [pers_rule]: "persistent (graph_ctxt \<kappa> g Mrk)"
  unfolding graph_ctxt_def by (rule cinv_persistent)

definition gmon_map :: "loc \<Rightarrow> chl \<Rightarrow> gmon" where "gmon_map l v = fmupd l (Ex v) fmempty"
notation gmon_map (infix "[\<mapsto>\<^sub>g]" 60)
end    