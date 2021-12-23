theory Mon
imports Graph 
  "../IrisCore/DerivedConstructions"
  "../IrisCore/Frac"
  "../HeapLang/HeapLang"
  "../HeapLang/Notation"
  "../HeapLang/PrimitiveLaws"
  "../IrisCore/BaseLogicShallow"
  "../IrisCore/PointTo"
begin

subsection \<open> The underlying structures of the spanning tree \<close>
text \<open> Based on https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/spanning_tree/mon.v \<close>

(* Children locations, in Coq it's a leibniz0 structure*)
type_synonym chl = "loc option\<times>loc option"

(* The graph camera, a unital camera. *)
type_synonym graphUR = "((loc\<rightharpoonup>(chl ex))\<times>frac) option"

(* A camera for duplicatable markings *)
type_synonym markingUR = "loc set"

(* 
  This would normally be a list of camera functors to allow for modular reasoning.
  Isabelle does not support type lists and thus we use a record for this simple example.  
*)
record graphG = 
  graph :: "graphUR auth"
  marking :: "markingUR auth"
  
instantiation graphG_ext :: (ofe) ofe begin
definition n_equiv_graphG_ext :: "nat \<Rightarrow> 'a graphG_scheme \<Rightarrow> 'a graphG_scheme \<Rightarrow> bool" where
  "n_equiv_graphG_ext n x y \<equiv> n_equiv n (graph x) (graph y) \<and> n_equiv n (marking x) (marking y)
    \<and> n_equiv n (more x) (more y)"
definition ofe_eq_graphG_ext :: "'a graphG_scheme \<Rightarrow> 'a graphG_scheme \<Rightarrow> bool" where
  "ofe_eq_graphG_ext x y \<equiv> ofe_eq (graph x) (graph y) \<and> ofe_eq (marking x) (marking y) 
    \<and> ofe_eq (more x) (more y)"
instance by standard 
(auto simp: n_equiv_graphG_ext_def ofe_eq_graphG_ext_def ofe_refl ofe_sym ofe_limit intro: ofe_trans ofe_mono)
end

instance graphG_ext :: (discrete) discrete 
  by standard (auto simp: n_equiv_graphG_ext_def ofe_eq_graphG_ext_def ofe_refl d_equiv d_eq)
  
instantiation graphG_ext :: (camera) camera begin
lift_definition valid_raw_graphG_ext :: "'a graphG_scheme \<Rightarrow> sprop" is
  "\<lambda>g n. n_valid (graph g) n \<and> n_valid (marking g) n \<and> n_valid (more g) n" by simp
definition pcore_graphG_ext :: "'a graphG_scheme \<Rightarrow> 'a graphG_scheme option" where
  "pcore_graphG_ext x = (case pcore (graph x) of Some g \<Rightarrow> 
    (case pcore (marking x) of Some m \<Rightarrow> (case pcore (more x) of Some y \<Rightarrow> 
      Some \<lparr>graph=g,marking=m,\<dots>=y\<rparr> | None \<Rightarrow> None) | None \<Rightarrow> None) | None \<Rightarrow> None)"
definition op_graphG_ext :: "'a graphG_scheme \<Rightarrow> 'a graphG_scheme \<Rightarrow> 'a graphG_scheme" where
  "op_graphG_ext x y = \<lparr>graph=(graph x)\<cdot>(graph y),marking=(marking x)\<cdot>(marking y),\<dots>=(more x)\<cdot>(more y)\<rparr>"
instance proof
show "non_expansive (valid_raw::'a graphG_scheme \<Rightarrow> sprop)"
  apply (rule non_expansiveI)
  apply (auto simp: valid_raw_graphG_ext.rep_eq n_equiv_graphG_ext_def n_equiv_sprop_def d_equiv)
  using n_valid_ne ofe_mono ofe_sym  by blast+
next
show "non_expansive (pcore::'a graphG_scheme \<Rightarrow> 'a graphG_scheme option)"
  by (rule non_expansiveI; auto simp: n_equiv_graphG_ext_def pcore_graphG_ext_def ofe_refl 
    n_equiv_option_def d_equiv split: option.splits)
  (metis n_equiv_option_def option.discI option.inject pcore_ne)+
next 
show "non_expansive2 (op::'a graphG_scheme \<Rightarrow> 'a graphG_scheme \<Rightarrow> 'a graphG_scheme)"
  by (rule non_expansive2I) (auto simp: n_equiv_graphG_ext_def op_graphG_ext_def)
next
fix a b c :: "'a graphG_ext"
show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)" by (auto simp: op_graphG_ext_def camera_assoc)
next
fix a b :: "'a graphG_ext"
show "a \<cdot> b = b \<cdot> a" by (auto simp: op_graphG_ext_def camera_comm)
next
fix a a' :: "'a graphG_ext"
show "pcore a = Some a' \<Longrightarrow> a' \<cdot> a = a" 
  by (auto simp: op_graphG_ext_def pcore_graphG_ext_def camera_pcore_id split: option.splits)
next
fix a a' :: "'a graphG_ext"
show "pcore a = Some a' \<Longrightarrow> pcore a' = pcore a" 
  by (auto simp: pcore_graphG_ext_def camera_pcore_idem split: option.splits)
next
fix a a' b :: "'a graphG_ext"
show "pcore a = Some a' \<Longrightarrow> \<exists>c. b = a \<cdot> c \<Longrightarrow> \<exists>b'. pcore b = Some b' \<and> (\<exists>c. b' = a' \<cdot> c)"
  apply (auto simp: pcore_graphG_ext_def op_graphG_ext_def camera_pcore_mono total_pcore split: option.splits)
  apply (metis option.distinct(1) total_pcore)
  apply (metis camera_pcore_mono option.distinct(1))
  by (metis (no_types, opaque_lifting) camera_pcore_mono option.inject select_convs(1) select_convs(2) select_convs(3))
next
fix a b :: "'a graphG_ext" fix n
show "Rep_sprop (valid_raw (a \<cdot> b)) n \<Longrightarrow> Rep_sprop (valid_raw a) n"
  by (auto simp: valid_raw_graphG_ext.rep_eq op_graphG_ext_def camera_valid_op)
next
fix a b c :: "'a graphG_ext" fix n
show "Rep_sprop (valid_raw a) n \<Longrightarrow> n_equiv n a (b \<cdot> c) \<Longrightarrow> 
  \<exists>c1 c2. a = c1 \<cdot> c2 \<and> n_equiv n c1 b \<and> n_equiv n c2 c"
  by (auto simp: valid_raw_graphG_ext.rep_eq op_graphG_ext_def n_equiv_graphG_ext_def)
  (metis select_convs(1) select_convs(2) select_convs(3) surjective  camera_extend)
qed
end

instance graphG_ext :: (dcamera) dcamera 
  apply (standard; auto simp: valid_def valid_raw_graphG_ext.rep_eq)
  using dcamera_valid_iff by blast+

instantiation graphG_ext :: (ucamera) ucamera begin
definition \<epsilon>_graphG_ext :: "'a graphG_scheme" where [simp]: "\<epsilon>_graphG_ext \<equiv> \<lparr>graph=\<epsilon>,marking=\<epsilon>,\<dots>=\<epsilon>\<rparr>"
instance apply standard 
  apply (auto simp: valid_raw_graphG_ext.rep_eq valid_def \<epsilon>_valid[unfolded valid_def])
  apply (auto simp: op_graphG_ext_def \<epsilon>_left_id)
  by (auto simp: pcore_graphG_ext_def \<epsilon>_pcore)
end

instance graphG_ext :: (ducamera) ducamera ..

abbreviation own_graph :: "graphUR auth \<Rightarrow> graphG iprop" ("Own\<^sub>g _") where
  "own_graph \<equiv> \<lambda>g. Own\<lparr>graph=g, marking=\<epsilon>\<rparr>"

abbreviation own_marking :: "markingUR auth \<Rightarrow> graphG iprop" ("Own\<^sub>m _") where
  "own_marking \<equiv> \<lambda>m. Own\<lparr>graph=\<epsilon>, marking=m\<rparr>"
  
lemma n_incl_fragm_l: "n_incl n (fragm {l}) a = (case a of Auth (b,c) \<Rightarrow> l\<in>c)"
  by (auto split: auth.splits)

text \<open> Marking Definitions \<close>
definition is_marked ::"loc \<Rightarrow> graphG iprop" where "is_marked l = Own\<^sub>m(fragm {l})"

lemma is_marked_split: "Own\<^sub>m(fragm {l}) = Own\<^sub>m(fragm {l} \<cdot> fragm {l})"
  by (auto simp: auth_frag_op[symmetric] op_set_def)

lemma dup_marked: "is_marked l \<stileturn>\<turnstile> is_marked l \<^emph> is_marked l"
proof -
from own_op have "Own(\<lparr>graph=\<epsilon>, marking=fragm {l}\<rparr>\<cdot>\<lparr>graph=\<epsilon>, marking=fragm {l}\<rparr>)
  \<stileturn>\<turnstile> Own\<^sub>m(fragm {l}) \<^emph> Own\<^sub>m(fragm {l})" by auto
then have "Own\<lparr>graph=\<epsilon>\<cdot>\<epsilon>, marking=fragm {l}\<cdot>fragm {l}\<rparr> \<stileturn>\<turnstile> Own\<^sub>m(fragm {l}) \<^emph> Own\<^sub>m(fragm {l})" 
  by (auto simp: op_graphG_ext_def)
then show ?thesis by (auto simp: is_marked_def is_marked_split[symmetric] \<epsilon>_left_id) 
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

definition own_graphUR :: "frac \<Rightarrow> gmon \<Rightarrow> graphG iprop" where
  "own_graphUR q G = Own\<^sub>g(fragm (Some (G,q)))"

record heapG = graphG + 
  heap :: heapGS

definition heap_owns :: "marked_graph \<Rightarrow> (loc\<rightharpoonup>loc) \<Rightarrow> heapGS iprop" where
  "heap_owns M markings = 
  folding_on.F 
  (\<lambda>(l,(b,cl)) pred. (\<exists>\<^sub>u(\<lambda>m. (\<upharpoonleft>(markings l = Some m)) 
    \<^emph> (l\<mapsto>\<^sub>u#[(m, children_to_val cl)]) 
    \<^emph> (m\<mapsto>\<^sub>u#[b]))) \<^emph> pred)
  \<upharpoonleft>True
  {(l,node) | l node. M l = Some node}"
end