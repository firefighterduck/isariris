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

lemma is_closed_subst: "\<lbrakk>is_closed_val v; is_closed_expr (insert x X) e\<rbrakk> \<Longrightarrow> is_closed_expr X (subst x v e)"
  "is_closed_val v \<Longrightarrow> is_closed_expr {} (Val v)"  
proof (induction e and v arbitrary: X)
  case (Rec x1 x2 e)
  then show ?case 
    by (smt (z3) cons_binder.simps(2) cons_binder_comm insertCI insert_absorb is_closed_expr.simps(3) subst.simps(3))
qed auto

lemma is_closed_subst': "\<lbrakk>is_closed_val v; is_closed_expr (x#\<^sub>bX) e\<rbrakk> \<Longrightarrow> is_closed_expr X (subst' x v e)"
using is_closed_subst subst'_def by (cases x) auto

lemma subst_is_closed: "\<lbrakk>is_closed_expr X e; x \<notin> X\<rbrakk> \<Longrightarrow> subst x es e = e"
sorry

end
