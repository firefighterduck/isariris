theory Locations
imports Main
begin

section \<open> Locations \<close>
text \<open> Based on https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/locations.v \<close>

datatype loc = Loc (loc_car: int)

definition loc_add :: "loc \<Rightarrow> int \<Rightarrow> loc" (infixl "+\<^sub>\<iota>" 60) where
  "loc_add l off = Loc (loc_car l + off)"

lemma loc_add_assoc:  "l +\<^sub>\<iota> i +\<^sub>\<iota> j = l +\<^sub>\<iota> (i + j)"
  by (simp add: loc_add_def)

lemma loc_add_0: "l +\<^sub>\<iota> 0 = l"
  by (simp add: loc_add_def)

definition fresh_locs :: "loc list \<Rightarrow> loc" where
  "fresh_locs ls = Loc (fold (\<lambda>k r. max (1+loc_car k) r) ls 1)"

locale fresh_loc_properties
begin
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
    by (induction ls) (auto, simp add: less_le_trans fresh_loc_cons_mono max_fold_mono fold_simps(2))
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
  hence "loc_car (fresh_locs ls +\<^sub>\<iota> i) < loc_car (fresh_locs ls)" by (rule fresh_loc_properties.fresh_locs_strict)
  with assms show "False" by (simp add: loc_add_def)
qed
end