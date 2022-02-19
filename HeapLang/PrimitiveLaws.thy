theory PrimitiveLaws
imports HeapLang "../IrisCore/Frac" "../IrisCore/ProphMap"
begin

section \<open> Basic laws for HeapLang programs \<close>
text \<open> Based on \<^url>\<open>https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/primitive_laws.v\<close> \<close>

instantiation expr and val :: ofe begin
definition n_equiv_expr :: "nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" where [simp]: "n_equiv_expr \<equiv> \<lambda>_. (=)"
definition ofe_eq_expr :: "expr \<Rightarrow> expr \<Rightarrow> bool" where [simp]: "ofe_eq_expr \<equiv> (=)"
definition n_equiv_val :: "nat \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where [simp]: "n_equiv_val \<equiv> \<lambda>_. (=)"
definition ofe_eq_val :: "val \<Rightarrow> val \<Rightarrow> bool" where [simp]: "ofe_eq_val \<equiv> (=)"
instance by standard auto 
end

instance expr and val :: discrete by standard auto

text \<open>The heap does not contain invariant locations to stay as simple as possible.\<close>
type_synonym ('l,'v) heap = "('l,'v) map_view"
type_synonym heap_lang_heap = "(loc, val option) heap"
type_synonym heap_lang_proph_map = "(proph_id, (val\<times>val)) proph_mapGS"
type_synonym heap_lang_proph_map_raw = "(proph_id,(val\<times>val) list) fmap"
type_synonym heap_lang_proph_val_list = "(proph_id\<times>(val\<times>val)) list"
end