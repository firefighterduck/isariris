theory Metatheory
imports State
begin

section \<open> Metatheory \<close>
text \<open> Meta theory about HeapLang; 
  based on https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/metatheory.v\<close>

fun cons_binder :: "binder_t \<Rightarrow> string set \<Rightarrow> string set" (infixr "#\<^sub>b" 60) where
  "None#\<^sub>bbs = bs"
| "(Some b)#\<^sub>bbs = insert b bs"

lemma cons_binder_comm: "a#\<^sub>bb#\<^sub>bl=b#\<^sub>ba#\<^sub>bl"
 by (cases a; cases b) auto

function is_closed_expr :: "string set \<Rightarrow> expr \<Rightarrow> bool" 
  and is_closed_val :: "val \<Rightarrow> bool" where
  "is_closed_expr _ (Val v) =  is_closed_val v"
| "is_closed_expr X (Var x) = (x \<in> X)"
| "is_closed_expr X (Rec f x e) = is_closed_expr (f #\<^sub>b x #\<^sub>b X) e"
| "is_closed_expr X (UnOp _ e) = is_closed_expr X e"
| "is_closed_expr X (Fst e) = is_closed_expr X e" 
| "is_closed_expr X (Snd e) = is_closed_expr X e" 
| "is_closed_expr X (InjL e) = is_closed_expr X e" 
| "is_closed_expr X (InjR e) = is_closed_expr X e" 
| "is_closed_expr X (Fork e) = is_closed_expr X e" 
| "is_closed_expr X (Free e) = is_closed_expr X e" 
| "is_closed_expr X (Load e) = is_closed_expr X e"
| "is_closed_expr X (App e1 e2) = (is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (BinOp _ e1 e2) = (is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (Pair e1 e2) = (is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (AllocN e1 e2) = (is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (Store e1 e2) = (is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (Xchg e1 e2) = (is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (FAA e1 e2) = (is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (If e0 e1 e2)
  = (is_closed_expr X e0 \<and> is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (Case e0 e1 e2)
  = (is_closed_expr X e0 \<and> is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (CmpXchg e0 e1 e2)
  = (is_closed_expr X e0 \<and> is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X (Resolve e0 e1 e2)
  = (is_closed_expr X e0 \<and> is_closed_expr X e1 \<and> is_closed_expr X e2)"
| "is_closed_expr X NewProph = True"
(* is_closed_val *)
| "is_closed_val (LitV _) = True"
| "is_closed_val (RecV f x e) = is_closed_expr (f #\<^sub>b x #\<^sub>b {}) e"
| "is_closed_val (PairV v1 v2) = (is_closed_val v1 \<and> is_closed_val v2)"
| "is_closed_val (InjLV v) = is_closed_val v" 
| "is_closed_val (InjRV v) = is_closed_val v"
by pat_completeness auto
termination by lexicographic_order

lemma is_closed_weaken: "\<lbrakk>is_closed_expr X e; X \<subseteq> Y\<rbrakk> \<Longrightarrow> is_closed_expr Y e"
proof(induction e arbitrary: X Y)
  case (Rec f x b)
  from Rec(2) have "is_closed_expr (f #\<^sub>b x #\<^sub>b X) b" by simp
  moreover from Rec(3) have "(f #\<^sub>b x #\<^sub>b X) \<subseteq> (f #\<^sub>b x #\<^sub>b Y)" 
    using set_ConsD by (cases f; cases x) auto
  ultimately show ?case using Rec(1) by simp
qed auto

lemma is_closed_weaken_nil: "is_closed_expr {} e \<Longrightarrow> is_closed_expr X e"
  using is_closed_weaken by fastforce

lemma is_closed_subst: "\<lbrakk>is_closed_val v; is_closed_expr (insert x X) e\<rbrakk> 
  \<Longrightarrow> is_closed_expr X (subst x v e)"  
proof (induction e arbitrary: X)
  case (Rec x1 x2 e)
  then show ?case
    by (smt (verit, best) cons_binder.simps(2) cons_binder_comm insert_absorb2 is_closed_expr.simps(3) subst.simps(3))
qed auto

lemma is_closed_subst': "\<lbrakk>is_closed_val v; is_closed_expr (x#\<^sub>bX) e\<rbrakk> \<Longrightarrow> is_closed_expr X (subst' x v e)"
using is_closed_subst subst'_def by (cases x) auto

(* Substitution *)
lemma subst_is_closed: "\<lbrakk>is_closed_expr X e; x \<notin> X\<rbrakk> \<Longrightarrow> subst x es e = e"
proof (induction e arbitrary: X)
  case (Rec x1 x2 e)
  then show ?case by (cases x1; cases x2) auto
qed auto

lemma subst_is_closed_nil: "is_closed_expr {} e \<Longrightarrow> subst x v e = e"
using subst_is_closed by simp

lemma subst_subst: "subst x v (subst x v' e) = subst x v' e"
by (induction e) auto

lemma subst_subst': "subst' x v (subst' x v' e) = subst' x v' e"
by (cases x) (auto simp: subst'_def subst_subst)

lemma subst_subst_ne: "x \<noteq> y \<Longrightarrow> subst x v (subst y v' e) = subst y v' (subst x v e)"
by (induction e) auto

lemma subst_subst_ne': "x \<noteq> y \<Longrightarrow> subst' x v (subst' y v' e) = subst' y v' (subst' x v e)"
by (cases x; cases y) (auto simp: subst'_def subst_subst_ne)

lemma subst_rec': "x = f \<or> x = y \<or> x = None \<Longrightarrow> subst' x v (Rec f y e) = Rec f y e"
by (cases x) (auto simp: subst'_def)

lemma subst_rec_ne': "\<lbrakk>x \<noteq> f \<or> f = None; x \<noteq> y \<or> y = None\<rbrakk> \<Longrightarrow>
  subst' x v (Rec f y e) = Rec f y (subst' x v e)"
  by (cases x) (auto simp: subst'_def)

lemma bin_op_eval_closed: "\<lbrakk>is_closed_val v1; is_closed_val v2; bin_op_eval op v1 v2 = Some v'\<rbrakk> \<Longrightarrow>
  is_closed_val v'" unfolding bin_op_eval_def by (cases op; auto split: val.splits base_lit.splits) 
  (metis is_closed_val.simps(1) option.inject option.simps(3))

definition map_forall :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a,'b) map \<Rightarrow> bool" where
  "map_forall P m = (\<forall>k v. (m k = Some v) \<longrightarrow> P k v)"  

definition option_map_or :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b" where
  "option_map_or f b a = (case a of Some a \<Rightarrow> f a | None \<Rightarrow> b)"

lemma heap_closed_alloc: "\<lbrakk>0 < n; is_closed_val w; 
  map_forall (\<lambda>_ v. option_map_or is_closed_val True v) (heap \<sigma>);
  (\<forall> i::int. (0 \<le> i) \<longrightarrow> (i < n) \<longrightarrow> heap \<sigma> (l +\<^sub>\<iota> i) = None)\<rbrakk> \<Longrightarrow>
  map_forall (\<lambda>_ v. option_map_or is_closed_val True v) (heap \<sigma> ++ heap_array l (replicate (nat n) w))"
proof (auto simp: map_forall_def option_map_or_def loc_add_def split: option.splits)
  have "(heap_array l (replicate (nat n) w) k = Some (Some v)) \<Longrightarrow> w=v" for k v
    using heap_array_lookup[of l "(replicate (nat n) w)" k v]
    by (metis heap_array_elements in_set_replicate)
  then show "\<And>k x2.
    \<forall>k v. heap \<sigma> k = Some v \<longrightarrow> (\<forall>x2. v = Some x2 \<longrightarrow> is_closed_val x2) \<Longrightarrow>
    \<forall>i\<ge>0. i < n \<longrightarrow> heap \<sigma> (Loc (loc_car l + i)) = None \<Longrightarrow> 0 < n \<Longrightarrow> is_closed_val w \<Longrightarrow> 
      heap_array l (replicate (nat n) w) k = Some (Some x2) \<Longrightarrow> is_closed_val x2"
    by blast
qed

lemma head_step_is_closed: "\<lbrakk> e1 \<sigma>1 obs \<Rightarrow>\<^sub>h e2 \<sigma>2 es; is_closed_expr {} e1; 
  map_forall (\<lambda>_ v. option_map_or is_closed_val True v) (heap \<sigma>1)\<rbrakk> \<Longrightarrow>
  is_closed_expr {} e2 \<and> list_all (is_closed_expr {}) es \<and>
  map_forall (\<lambda>_ v. option_map_or is_closed_val True v) (heap \<sigma>2)"
proof (induction rule: head_step.induct)
  case (BetaS e' x v2 f e1 \<sigma>)
  then show ?case using is_closed_subst' by force
next
  case (UnOpS op v v' \<sigma>)
  then show ?case by (induction op v rule: un_op_eval.induct) auto
next
  case (BinOpS op v1 v2 v' \<sigma>)
  then show ?case using bin_op_eval_closed is_closed_expr.simps(1,13) list_all_simps(2) by blast
next
  case (AllocNS n \<sigma> l v)
  then show ?case
    apply (simp add: state_init_heap_def state_upd_heap_def split: option.splits)
    apply (rule heap_closed_alloc[of n v \<sigma> l, OF AllocNS(1)])
    by (auto simp: loc_add_def)
next
  case (NewProphS p \<sigma>)
  then show ?case by (simp add: state_upd_used_proph_id_def)
qed (auto simp: option_map_or_def map_forall_def subst'_def state_upd_heap_def split: option.splits)

definition binder_delete :: "binder_t \<Rightarrow> (string,'a) map \<Rightarrow> (string,'a) map" where
  "binder_delete b m = (case b of Some b \<Rightarrow> m(b:=None) | None \<Rightarrow> m)"

definition binder_insert :: "binder_t \<Rightarrow> 'a \<Rightarrow> (string, 'a) map \<Rightarrow> (string, 'a) map" where
  "binder_insert b a m = (case b of Some b \<Rightarrow> m(b\<mapsto>a) | None \<Rightarrow> m)"

fun subst_map :: "(string,val) map \<Rightarrow> expr \<Rightarrow> expr" where
  "subst_map _ (Val v) = Val v"
| "subst_map vs (Var y) = (case vs y of Some v \<Rightarrow> Val v | _ \<Rightarrow> Var y)"
| "subst_map vs (Rec f y e) = Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)"
| "subst_map vs (App e1 e2) = App (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (UnOp op e) = UnOp op (subst_map vs e)"
| "subst_map vs (BinOp op e1 e2) = BinOp op (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (If e0 e1 e2) = If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (Pair e1 e2) = Pair (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (Fst e) = Fst (subst_map vs e)"
| "subst_map vs (Snd e) = Snd (subst_map vs e)"
| "subst_map vs (InjL e) = InjL (subst_map vs e)"
| "subst_map vs (InjR e) = InjR (subst_map vs e)"
| "subst_map vs (Case e0 e1 e2) = Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (Fork e) = Fork (subst_map vs e)"
| "subst_map vs (AllocN e1 e2) = AllocN (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (Free e) = Free (subst_map vs e)"
| "subst_map vs (Load e) = Load (subst_map vs e)"
| "subst_map vs (Store e1 e2) = Store (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (Xchg e1 e2) = Xchg (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (CmpXchg e0 e1 e2) = CmpXchg (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs (FAA e1 e2) = FAA (subst_map vs e1) (subst_map vs e2)"
| "subst_map vs NewProph = NewProph"
| "subst_map vs (Resolve e0 e1 e2) = Resolve (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)"

lemma subst_map_empty[simp]: "subst_map Map.empty e = e"
by (induction e) (auto simp: binder_delete_def split: option.splits)

lemma subst_map_insert: "subst_map (vs(x\<mapsto>v)) e = subst x v (subst_map (vs(x:=None)) e)"
  by (induction e arbitrary: vs; auto simp: binder_delete_def fun_upd_twist split: option.splits)
    (metis fun_upd_twist)

lemma subst_map_singleton: "subst_map [x\<mapsto>v] e = subst x v e"
by (simp add: subst_map_insert binder_delete_def)

lemma subst_map_binder_insert: 
  "subst_map (binder_insert b v vs) e = subst' b v (subst_map (binder_delete b vs) e)"
by (auto simp: binder_insert_def subst'_def binder_delete_def subst_map_insert split: option.splits)

lemma binder_delete_empty: "binder_delete b Map.empty = Map.empty"
by (cases b; simp add: binder_delete_def)

lemma subst_map_binder_insert_empty: "subst_map (binder_insert b v Map.empty) e = subst' b v e"
by (rule subst_map_binder_insert[where ?vs = Map.empty, simplified binder_delete_empty subst_map_empty])

lemma subst_map_binder_insert_2: "subst_map (binder_insert b1 v1 (binder_insert b2 v2 vs)) e =
  subst' b2 v2 (subst' b1 v1 (subst_map (binder_delete b2 (binder_delete b1 vs)) e))"
proof (cases b1)
  case None
  then show ?thesis by (cases b2)
    (auto simp: binder_delete_def binder_insert_def subst'_def subst_map_insert)
next
  case (Some a)
  then show ?thesis proof (cases b2)
    case None
    then show ?thesis 
      by (auto simp: binder_delete_def binder_insert_def subst'_def subst_map_insert split: option.splits)
  next
    case (Some b)
    then show ?thesis apply (cases "a=b") 
    apply (simp_all add: binder_delete_def binder_insert_def subst'_def subst_map_insert split: option.splits)
    apply (metis fun_upd_twist fun_upd_upd subst_map_insert subst_subst subst_subst_ne)
    by (metis fun_upd_twist fun_upd_upd subst_map_insert subst_subst)
  qed    
qed 

lemma subst_map_binder_insert_2_empty: 
  "subst_map (binder_insert b1 v1 (binder_insert b2 v2 Map.empty)) e =  subst' b2 v2 (subst' b1 v1 e)"
by (rule subst_map_binder_insert_2[where ?vs=Map.empty, simplified binder_delete_empty subst_map_empty])

lemma subst_map_is_closed: "\<lbrakk>is_closed_expr X e; \<forall>x \<in> X. vs x = None\<rbrakk> \<Longrightarrow> subst_map vs e = e"
proof (induction e arbitrary: X vs)
  case (Rec x1 x2 e)
  then show ?case by (cases x1; cases x2) (auto simp: binder_delete_def)
qed auto

lemma subst_map_is_closed_nil: "is_closed_expr {} e \<Longrightarrow> subst_map vs e = e"
using subst_map_is_closed by blast
end
