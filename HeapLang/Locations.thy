theory Locations
imports "../IrisCore/OFEs"
begin

section \<open> Locations \<close>
text \<open> Based on \<^url>\<open>https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/locations.v\<close> \<close>

datatype loc = Loc (loc_car: int)

instantiation loc :: ord begin
definition less_eq_loc :: "loc \<Rightarrow> loc \<Rightarrow> bool" where
  "less_eq_loc l1 l2 = ((loc_car l1) \<le> (loc_car l2))"
definition less_loc :: "loc \<Rightarrow> loc \<Rightarrow> bool" where
  "less_loc l1 l2 = ((loc_car l1) < (loc_car l2))"
instance ..
end
                           
instantiation loc :: linorder begin
instance proof qed (auto simp: less_eq_loc_def less_loc_def loc.expand)
end

definition loc_add :: "loc \<Rightarrow> int \<Rightarrow> loc" (infixl "+\<^sub>\<iota>" 60) where
  "loc_add l off = Loc (loc_car l + off)"

lemma loc_add_assoc:  "l +\<^sub>\<iota> i +\<^sub>\<iota> j = l +\<^sub>\<iota> (i + j)"
  by (simp add: loc_add_def)

lemma loc_add_0: "l +\<^sub>\<iota> 0 = l"
  by (simp add: loc_add_def)

lemma loc_ranges: "{(l+\<^sub>\<iota>i) |i. i\<in>{0..<n}} = {l..<(l+\<^sub>\<iota>n)}"
  by (auto simp: less_eq_loc_def less_loc_def loc_add_def, smt (z3) loc.exhaust_sel)

lemma loc_set_lift: "ls = Loc ` (loc_car ` ls)"
  unfolding image_def by auto

lemma loc_set_lift': "loc_car ` {l..<u::loc} = {loc_car l..<loc_car u}"
  apply (auto simp: less_eq_loc_def less_loc_def)
  by (metis atLeastLessThan_iff image_eqI less_eq_loc_def linorder_not_le loc.sel)

lemma finite_atLeastLessThan_loc [iff]: "finite {l..<u::loc}"
apply (subst loc_set_lift[of "{l..<u::loc}"])
apply (rule finite_imageI)
unfolding loc_set_lift'
by (rule finite_atLeastLessThan_int)

definition fresh_locs :: "loc list \<Rightarrow> loc" where
  "fresh_locs ls = Loc (fold (\<lambda>k r. max (1+loc_car k) r) ls 1)"

locale fresh_loc_properties begin
lemma max_fold_mono: 
  "l\<le>u \<Longrightarrow> fold (\<lambda>k r. max (1+loc_car k) r) ls l \<le> fold (\<lambda>k r. max (1+loc_car k) r) ls u"
  by (induction ls arbitrary: l u) auto

lemma fresh_loc_cons_mono: "loc_car (fresh_locs ls) \<le> loc_car (fresh_locs (l#ls))"
  by (simp add: fresh_locs_def max_fold_mono)

lemma fresh_locs_strict: "l \<in> set ls \<Longrightarrow> loc_car l < loc_car (fresh_locs ls)"
proof (induction ls)
case (Cons a ls)
  then show ?case proof (cases "l=a")
    case True
    have aux: "x < fold (\<lambda>k r. max (1+loc_car k) r) ls (max (1+x) 1)" for x
      by (induction ls; auto) (smt (verit, best) max_fold_mono)
    from True show ?thesis by (simp add: fresh_locs_def)(rule aux[of "loc_car a"])
  next
    case False
    with Cons fresh_loc_cons_mono order_less_le_trans show ?thesis by fastforce
  qed
qed (simp)
end

lemma fresh_locs_fresh: 
  assumes "(0 \<le> i)" 
  shows "fresh_locs ls +\<^sub>\<iota> i \<notin> (set ls)"
proof
  assume "fresh_locs ls +\<^sub>\<iota> i \<in> set ls"
  hence "loc_car (fresh_locs ls +\<^sub>\<iota> i) < loc_car (fresh_locs ls)" 
    by (rule fresh_loc_properties.fresh_locs_strict)
  with assms show "False" by (simp add: loc_add_def)
qed

instantiation loc :: ofe begin
definition n_equiv_loc :: "nat \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> bool" where "n_equiv_loc _ \<equiv> (=)"
definition ofe_eq_loc :: "loc \<Rightarrow> loc \<Rightarrow> bool" where "ofe_eq_loc \<equiv> (=)"
instance by standard (auto simp: n_equiv_loc_def ofe_eq_loc_def)
end

instance loc :: discrete by standard (auto simp: n_equiv_loc_def ofe_eq_loc_def)
end