theory FracAuth
imports View
begin

type_synonym 'a frac_auth = "(frac \<times> 'a) option view"

definition frac_auth_auth :: "'a::camera \<Rightarrow> 'a frac_auth" ("\<Zspot>F _") where 
  "frac_auth_auth x = \<Zspot>A (Some (1,x))"

definition frac_auth_frag :: "frac \<Rightarrow> 'a::camera \<Rightarrow> 'a frac_auth" ("\<circle>F{_} _") where
  "frac_auth_frag q x = \<circle>A (Some (q,x))"

lemma frac_auth_frag_op: "\<circle>F{q} x \<cdot> \<circle>F{p} y = \<circle>F{q+p} (x\<cdot>y)"
by (auto simp: op_view_def frac_auth_frag_def view_frag_def op_option_def op_prod_def op_frac_def 
  plus_frac_def)

lemma int_lup: "x+y'=x'+(y::int) \<Longrightarrow> (x,y)\<leadsto>\<^sub>L(x',y')"
  by (auto simp: lup_def valid_raw_int_def op_int_def)

lemma int_frac_lup:"(x::int,y)\<leadsto>\<^sub>L(x',y') \<Longrightarrow> (Some (1::frac,x),Some (q,y))\<leadsto>\<^sub>L(Some (1,x'),Some (q,y'))"
apply (auto simp: lup_def valid_raw_option_def op_option_def prod_n_valid_def n_equiv_option_def
  d_equiv valid_raw_int_def)
subgoal for n c apply (cases c) by (auto simp: op_prod_def d_equiv op_int_def)
done

lemma int_fa_lup: "\<lbrakk>x+y'=x'+(y::int)\<rbrakk> \<Longrightarrow> ((\<Zspot>F x) \<cdot> \<circle>F{q} y)\<leadsto>((\<Zspot>F x') \<cdot> \<circle>F{q} y')"
  unfolding frac_auth_frag_def frac_auth_auth_def
  apply (rule auth_update)
  apply (rule int_frac_lup)
  by (erule int_lup)

lemma valid_frac_auth_eq: "valid (\<Zspot>F (x::int) \<cdot> \<circle>F{1} y) \<Longrightarrow> x=y"
apply (auto simp: valid_def frac_auth_auth_def frac_auth_frag_def valid_raw_view.rep_eq op_view_def
  view_auth_def view_frag_def op_option_def \<epsilon>_option_def n_equiv_ag.rep_eq to_ag.rep_eq 
  n_equiv_option_def view_rel_def n_incl_def d_equiv valid_dfrac_own[unfolded valid_def])
proof -
fix c
assume "option_op (Some (1::frac, y)) c = Some (1, x)"
then show "x=y" apply (cases c) apply (auto simp: op_prod_def frac_op_plus)
  using frac_sum_one_le by blast
qed

lemma frac_auth_zero_valid: "valid \<Zspot>F (0::int)"
by (auto simp: valid_def valid_raw_view.rep_eq frac_auth_auth_def view_auth_def 
  valid_dfrac_own[unfolded valid_def] view_rel_def n_equiv_ag.rep_eq to_ag.rep_eq d_equiv
  n_equiv_option_def  valid_raw_option_def prod_n_valid_def valid_one_frac[unfolded valid_def]
  valid_raw_int_def)

lemma frac_frag_zero_valid: "valid \<circle>F{1} (0::int)"
apply (auto simp: valid_def valid_raw_view.rep_eq frac_auth_frag_def view_frag_def 
  valid_dfrac_own[unfolded valid_def] view_rel_def n_equiv_ag.rep_eq to_ag.rep_eq d_equiv
  n_equiv_option_def valid_raw_option_def prod_n_valid_def valid_one_frac[unfolded valid_def]
  valid_raw_int_def n_incl_def)
apply (auto simp: op_option_def)
by (metis option.simps(5) option_op.simps(2) prod_n_valid_fun_def sPure.rep_eq valid_frac 
  valid_one_frac valid_raw_int_def)

end