theory Mon
imports Graph 
  "../IrisCore/DerivedConstructions"
  "../IrisCore/Frac"
  "../HeapLang/HeapLang"
  "../HeapLang/Notation"
  "../IrisCore/BaseLogicShallow"
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
  Isabelle does not support type lists and thus we use a product for this simple example.  
*)
type_synonym graphG = "(markingUR auth\<times>graphUR auth)"

lemma n_incl_fragm_l: "n_incl n (fragm {l}) a = (case a of Auth (b,c) \<Rightarrow> l\<in>c)"
  by (auto split: auth.splits)

text \<open> Marking Definitions \<close>
definition is_marked ::"loc \<Rightarrow> graphG iprop" where "is_marked l = Own((fragm {l},\<epsilon>))"

lemma dup_marked: "is_marked l \<stileturn>\<turnstile> is_marked l \<^emph> is_marked l"
proof (rule upred_entail_eqI; auto simp: is_marked_def upred_sep.rep_eq upred_own.rep_eq n_incl_fragm_l split: auth.splits)
  fix a1 a2 b n
  assume assms: "l \<in> a2"
  define c1 c2 where cs: "c1 \<equiv> Auth (a1,a2)" "c2 \<equiv> Auth (None,a2)"
  have "n_equiv n (Auth (a1, a2), b) ((Auth (a1, a2), b) \<cdot> (fragm a2,\<epsilon>))"
    apply (auto simp: op_prod_def \<epsilon>_right_id ofe_refl op_auth_def op_set_def split:auth.splits)
    by (metis \<epsilon>_option_def \<epsilon>_right_id ofe_eq_limit)
  with cs assms(1) show "\<exists>a. \<forall>ab bb. a = Auth (ab, bb) \<longrightarrow> (\<exists>bc a. \<forall>ac bd. a = Auth (ac, bd) \<longrightarrow> 
  (\<exists>be. n_equiv n (Auth (a1, a2), b) ((Auth (ab, bb), bc) \<cdot> (Auth (ac, bd), be))) \<and> l \<in> bb \<and> l \<in> bd)"
    by blast
next
  fix x x1 x2 y n
  assume assms:
    "\<forall>a bb. x = Auth (a, bb) \<longrightarrow> (\<exists>bc aa. \<forall>ac bd. aa = Auth (ac, bd) \<longrightarrow> 
    (\<exists>be. n_equiv n (Auth (x1, x2), y) ((Auth (a, bb), bc) \<cdot> (Auth (ac, bd), be))) \<and> l \<in> bb \<and> l \<in> bd)"
  obtain a1 a2 where "x=Auth (a1,a2)" using auth.exhaust by auto
  with assms have "(\<exists>bc aa. \<forall>ac bd. aa = Auth (ac, bd) \<longrightarrow> 
    (\<exists>be. n_equiv n (Auth (x1, x2), y) ((Auth (a1, a2), bc) \<cdot> (Auth (ac, bd), be))) \<and> l \<in> a2 \<and> l \<in> bd)"
    by simp
  then obtain bc aa where aa: "\<forall>ac bd. aa = Auth (ac, bd) \<longrightarrow> 
    (\<exists>be. n_equiv n (Auth (x1, x2), y) ((Auth (a1, a2), bc) \<cdot> (Auth (ac, bd), be))) \<and> l \<in> a2 \<and> l \<in> bd"
    by blast
  obtain ac bd where "aa = Auth (ac,bd)" using auth.exhaust by auto
  with aa have "(\<exists>be. n_equiv n (Auth (x1, x2), y) ((Auth (a1, a2), bc) \<cdot> (Auth (ac, bd), be))) \<and> l \<in> a2 \<and> l \<in> bd"
    by simp
  then obtain be where be: "(n_equiv n (Auth (x1, x2), y) ((Auth (a1, a2), bc) \<cdot> (Auth (ac, bd), be)))" 
    "l \<in> a2" "l \<in> bd" by auto
  then have "n_equiv n x2 (a2\<cdot>bd)" by (auto simp: op_auth_def op_prod_def)
  then have "x2=a2\<union>bd" by (auto simp: n_equiv_set_def op_set_def)
  with be(2,3) show "l\<in>x2" by simp
qed
(* More tbd *)

text \<open> Another monoid for graphs?  \<close>
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
end