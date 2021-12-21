theory PrimitiveLaws
imports State "../IrisCore/BaseLogicShallow"
begin

section \<open> Basic laws for HeapLang programs \<close>
text \<open> Based on https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/primitive_laws.v \<close>

instantiation expr and val :: ofe begin
definition n_equiv_expr :: "nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" where [simp]: "n_equiv_expr \<equiv> \<lambda>_. (=)"
definition ofe_eq_expr :: "expr \<Rightarrow> expr \<Rightarrow> bool" where [simp]: "ofe_eq_expr \<equiv> (=)"
definition n_equiv_val :: "nat \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where [simp]: "n_equiv_val \<equiv> \<lambda>_. (=)"
definition ofe_eq_val :: "val \<Rightarrow> val \<Rightarrow> bool" where [simp]: "ofe_eq_val \<equiv> (=)"
instance by standard auto 
end

instance expr and val :: discrete by standard auto

end