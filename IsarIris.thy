theory IsarIris
imports "SpinLock/Demo"
begin

type_synonym 'a iquant = "'a \<Rightarrow> iprop"

definition base_tele :: "'a iquant" where "base_tele _ \<equiv> upred_emp"
definition telescope :: "'a iquant \<Rightarrow> ('a\<times>'b) iquant \<Rightarrow> ('a\<times>'b) iquant" where
  "telescope P T tupl = (case tupl of (x,y) \<Rightarrow> (P x) \<^emph> (T (x,y)))"

lemma "(\<exists>\<^sub>u p. telescope P T p) = (\<exists>\<^sub>u x. P x \<^emph> (\<exists>\<^sub>u y. T (x,y)))"
unfolding telescope_def upred_entail_eq_def
apply transfer'
apply (auto simp: op_prod_def prod_n_valid_def)
by meson
end
