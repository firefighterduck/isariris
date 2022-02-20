theory Mon
imports SpanningTreeCameras
  "../IrisCore/Invariant"
  "../HeapLang/Notation"
  "../IrisCore/Misc"
  "../IrisCore/AuthHeap"
begin

subsection \<open> The underlying structures of the spanning tree \<close>
text \<open> Based on \<^url>\<open>https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/spanning_tree/mon.v\<close> \<close>

definition graphN :: namespace where "graphN = add_name nroot (string_to_name ''SPT_graph'')"
abbreviation own_graph :: "graphUR auth \<Rightarrow> iprop" ("Own\<^sub>g _" 85) where
  "own_graph g \<equiv> Own(constr_graph g)"
abbreviation own_marking :: "markingUR auth \<Rightarrow> iprop" ("Own\<^sub>m _" 85) where
  "own_marking m \<equiv> Own(constr_markings m)"

lemma n_incl_fragm_l: "n_incl n (fragm {l}) a = (case a of Auth (b,c) \<Rightarrow> l\<in>c)"
  by (auto split: auth.splits)

text \<open> Marking Definitions \<close>
definition is_marked ::"loc \<Rightarrow> iprop" where "is_marked l = Own\<^sub>m(fragm {l})"

lemma is_marked_split: "Own\<^sub>m(fragm {l}) = Own\<^sub>m(fragm {l} \<cdot> fragm {l})"
  by (auto simp: auth_frag_op[symmetric] op_set_def)

lemma dup_marked: "is_marked l \<stileturn>\<turnstile> is_marked l \<^emph> is_marked l"
proof -
from own_op have "Own (constr_markings (fragm {l}) \<cdot> constr_markings (fragm {l})) 
    \<stileturn>\<turnstile> (Own\<^sub>m(fragm {l})) \<^emph> Own\<^sub>m(fragm {l})" 
  by auto
then have "Own(constr_markings (fragm {l}\<cdot>fragm {l})) \<stileturn>\<turnstile> Own\<^sub>m(fragm {l}) \<^emph> Own\<^sub>m(fragm {l})" 
  by (auto simp add: op_prod_def \<epsilon>_left_id constr_markings_def simp del: \<epsilon>_dset_def \<epsilon>_dfset_def \<epsilon>_option_def)
then show ?thesis unfolding is_marked_split[symmetric] by (simp add: is_marked_def)
qed

type_synonym gmon = "loc\<rightharpoonup>(chl ex)"

fun excl_chlC_chl :: "chl ex \<Rightarrow> chl option" where
  "excl_chlC_chl (Ex w) = Some w"
| "excl_chlC_chl ex.Inv = None"

definition gmon_graph :: "gmon \<Rightarrow> loc graph" where 
  "gmon_graph g = (\<lambda>l. Option.bind l excl_chlC_chl) \<circ> g"
lemma gmon_graph_dom: "valid g \<Longrightarrow> (dom (gmon_graph g) = dom g)"
  by (auto simp: gmon_graph_def valid_def valid_raw_fun_def valid_raw_option_def bind_eq_Some_conv 
  Abs_sprop_inverse valid_raw_ex_def split: ex.splits option.splits) (metis excl_chlC_chl.elims surj_pair)

fun child_to_val :: "loc option \<Rightarrow> val" where
  "child_to_val None = NoneV"
| "child_to_val (Some l) = SomeV (LitV (LitLoc l))"

definition children_to_val :: "chl \<Rightarrow> val" where
  "children_to_val chs = PairV (child_to_val (fst chs)) (child_to_val (snd chs))"

type_synonym marked_graph = "loc\<rightharpoonup>(bool\<times>chl)"

definition of_graph_elem :: "gmon \<Rightarrow> loc \<Rightarrow> chl \<Rightarrow> (bool\<times>chl) option" where
  "of_graph_elem g l v = (case gmon_graph g l of Some w \<Rightarrow> Some (True,w) | None \<Rightarrow> Some (False, v))"

definition of_graph :: "loc graph \<Rightarrow> gmon \<Rightarrow> marked_graph" where
  "of_graph g G l = Option.bind (g l) (\<lambda>chl. of_graph_elem G l chl)"

definition own_graphUR :: "frac \<Rightarrow> gmon \<Rightarrow> iprop" where
  "own_graphUR q G = Own\<^sub>g(fragm (Some (G,q)))"

context includes points_to_syntax begin
definition heap_owns :: "marked_graph \<Rightarrow> (loc\<rightharpoonup>loc) \<Rightarrow> iprop" where
  "heap_owns M markings = 
  sep_map_set (\<lambda>(l,(b,cl)). (\<exists>\<^sub>u m. ((\<upharpoonleft>(markings l = Some m))
    \<^emph> (l\<mapsto>\<^sub>u#[(m, children_to_val cl)])
    \<^emph> (m\<mapsto>\<^sub>u#[b]))))
  {(l,node) | l node. M l = Some node}"
end

definition graph_inv :: "loc graph \<Rightarrow> (loc\<rightharpoonup>loc) \<Rightarrow> iprop" where
  "graph_inv g markings \<equiv> \<exists>\<^sub>u (G::gmon). ((Own\<^sub>g(full (Some (G, 1))))
    \<^emph> (Own\<^sub>m(full (dom G))) \<^emph> (heap_owns (of_graph g G) markings) 
    \<^emph> (\<upharpoonleft>(strict_subgraph g (gmon_graph G))))"

definition graph_ctxt :: "loc graph \<Rightarrow> (loc\<rightharpoonup>loc) \<Rightarrow> iprop" where 
  "graph_ctxt g Mrk \<equiv> cinv graphN (graph_inv g Mrk)"

lemma graph_ctxt_persistent: "persistent (graph_ctxt g Mrk)"
  unfolding graph_ctxt_def by (rule cinv_persistent)

definition gmon_map :: "loc \<Rightarrow> chl \<Rightarrow> gmon" where "gmon_map l v = [l\<mapsto>Ex v]"
notation gmon_map (infix "[\<mapsto>\<^sub>g]" 60)
end    