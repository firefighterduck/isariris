theory State
imports HeapLang
begin

section \<open> State \<close>
text \<open> State specific definitions and lemmata; 
       from https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lang.v \<close>

(* The state: heaps of val options, with None representing deallocated locations. *)
datatype state = State (heap: "(loc,val) map") (used_proph_id: "proph_id set")

definition state_upd_heap :: "((loc,val) map \<Rightarrow> (loc,val) map) \<Rightarrow> state \<Rightarrow> state" where
  "state_upd_heap f \<sigma> = State (f (heap \<sigma>)) (used_proph_id \<sigma>)"

definition state_upd_used_proph_id :: "(proph_id set \<Rightarrow> proph_id set) \<Rightarrow> state \<Rightarrow> state" where
  "state_upd_used_proph_id f \<sigma> = State (heap \<sigma>) (f (used_proph_id \<sigma>))"

fun heap_array :: "loc \<Rightarrow> val list \<Rightarrow> (loc, val) map" where
  "heap_array l [] = Map.empty"
| "heap_array l (v#vs) = (heap_array (l+\<^sub>\<iota>1) vs)(l\<mapsto>v)"
  
lemma heap_array_singleton: "heap_array l [v] = [l\<mapsto>v]" by simp

lemma heap_array_dom: "dom (heap_array l vs) = Loc ` {(loc_car l)..< (loc_car l) + int (length vs)}"
proof (induction vs arbitrary: l)
  case (Cons a vs)
  have "dom (heap_array l (a # vs)) = insert l (dom (heap_array (l+\<^sub>\<iota>1) vs))" by simp
  also have "... = insert l (Loc ` {(loc_car (l+\<^sub>\<iota>1))..< (loc_car (l+\<^sub>\<iota>1)) + int (length vs)})" 
    using Cons by simp
  also have "... = Loc ` ({loc_car l} \<union> {(loc_car (l+\<^sub>\<iota>1))..< (loc_car (l+\<^sub>\<iota>1)) + int (length vs)})" 
      by simp
  also have "... = Loc ` ({(loc_car l)..<(loc_car (l+\<^sub>\<iota>1))} \<union>
    {(loc_car (l+\<^sub>\<iota>1))..< (loc_car (l+\<^sub>\<iota>1)) + int (length vs)})" using loc_add_def by force
  also have "... = Loc ` ({(loc_car l)..<(loc_car l)+1} \<union>
    {(loc_car l)+1..< (loc_car l) + 1 + int (length vs)})" by (simp add: loc_add_def) 
  also have "... = Loc ` {(loc_car l)..< (loc_car l) + int (length (a#vs))}" by auto
  finally show ?case .
qed (simp)

lemma heap_array_shift: "heap_array l vs k = heap_array (l+\<^sub>\<iota>n) vs (k+\<^sub>\<iota>n)"
proof (induction vs arbitrary: l k)
  case (Cons a vs)
  show ?case apply auto using loc_add_def apply (simp add: loc.expand) using Cons using loc_add_def
  by (metis add.commute loc_add_assoc)
qed (simp)

lemma heap_array_cons_shift: "(heap_array l vs k = Some w) \<Longrightarrow> (heap_array l (v#vs) (k+\<^sub>\<iota>1) = Some w)"
proof -
  assume assm: "heap_array l vs k = Some w"
  hence "k \<in> dom (heap_array l vs)" by blast
  with heap_array_dom[of l vs] have "l\<noteq>k+\<^sub>\<iota>1" using loc_add_def by auto
  with assm show "heap_array l (v#vs) (k+\<^sub>\<iota>1) = Some w" unfolding loc_add_def apply auto 
  using heap_array_shift loc_add_def by fastforce
qed

lemma heap_array_elements: "heap_array l vs k = Some w \<Longrightarrow> w \<in> set vs"
proof (induction vs arbitrary: l k)
  case (Cons a vs)
  then show ?case by (metis fun_upd_apply heap_array.simps(2) in_set_member member_rec(1) option.inject)
qed (simp)

lemma heap_array_step: "\<lbrakk>heap_array l (v#vs) k = Some w; l\<noteq>k\<rbrakk> \<Longrightarrow> heap_array l vs (k+\<^sub>\<iota>(-1)) = Some w"
proof (induction vs arbitrary: l k v)
  case (Cons a vs)
  from Cons(3) have "heap_array l (v # a # vs) k = heap_array (l+\<^sub>\<iota>1) (a#vs) k" by simp
  with Cons(2) have step: "heap_array (l+\<^sub>\<iota>1) (a#vs) k = Some w" by simp
  then show ?case proof (cases "(l+\<^sub>\<iota>1=k)")
    case True
    with step have "w=a" by simp
    with True show ?thesis unfolding loc_add_def by auto
  next
    case False
    from Cons(3) have "heap_array l (a # vs) (k +\<^sub>\<iota> - 1) = heap_array (l+\<^sub>\<iota>1) vs (k +\<^sub>\<iota> - 1)"
      using loc_add_def False by force
    with Cons(1)[OF step False] show ?thesis by simp
  qed
qed (simp)

(* Due to nth being defined as primrec, this can't be an iff but only a one sided implication. *)
lemma heap_array_lookup: "((heap_array l vs) k = Some ow) \<Longrightarrow>
  (\<exists>j w. 0 \<le> j \<and> k = l +\<^sub>\<iota> j \<and> vs!(nat j) = w \<and> w=ow)"
proof (induction vs arbitrary: k)
  case (Cons a vs)
  then show ?case proof (cases "l=k")
    case True
    hence "heap_array l (a#vs) k = Some a" by simp
    with Cons(2) have "ow = a" by simp
    moreover from True have "k=l+\<^sub>\<iota>0 \<and> (0::int)\<le>0 \<and> (a#vs)!(nat 0) = a" by (simp add: loc_add_0)
    ultimately show ?thesis by blast
  next
    case False
    from Cons(1)[OF heap_array_step[OF Cons(2) False]] obtain j w 
      where jw: "0 \<le> j \<and> k +\<^sub>\<iota> - 1 = l +\<^sub>\<iota> j \<and> vs ! nat j = w \<and> w = ow" by blast
    hence "0\<le>j+1 \<and> k=l+\<^sub>\<iota>(j+1) \<and> (a#vs)!(nat (j+1)) = w \<and> w = ow" apply (simp add: loc_add_def)
      by (metis (no_types, hide_lams) Suc_nat_eq_nat_zadd1 diff_Suc_Suc diff_add_cancel diff_zero group_cancel.add2 loc.exhaust_sel)
    then show ?thesis by fast
  qed
qed (simp)

lemma state_array_map_disjoint: "(\<forall>i. (0\<le>i \<longrightarrow> (nat i < length vs) \<longrightarrow> h (l+\<^sub>\<iota>i) = None))
  \<Longrightarrow> dom (heap_array l vs) \<inter> dom h = {}"
proof
  assume assm: "\<forall>i\<ge>0. nat i < length vs \<longrightarrow> h (l +\<^sub>\<iota> i) = None"
  from assm have "\<forall>i\<ge>0. nat i < length vs \<longrightarrow> (l +\<^sub>\<iota> i) \<notin> dom h" by fastforce
  with heap_array_dom have "\<forall>k\<in>dom (heap_array l vs). k \<notin> dom h"
  by (smt (verit, best) atLeastLessThan_iff domD heap_array_lookup imageE loc.inject loc_add_def nat_less_iff)
  then show "dom (heap_array l vs) \<inter> dom h \<subseteq> {}" by auto
qed (simp)
end