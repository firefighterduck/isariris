theory LogicSyntaxDeep
imports CoreStructures
begin
(* The Coq formalization also used the empty type but I have no idea why 
  or whether HOL has such a type. Cmra is the carrier type of the underlying camera. *)
datatype logic_type = PropT | CmraT | UnitT | ProdT logic_type logic_type
  | FunT logic_type logic_type (infixr "\<rightarrow>" 15)
  (* These types are relevant for arguing about HeapLang programs*)
  | Expr | State | Observation | List logic_type

datatype 'x::ucamera logic_term = 
  VarL string
| Unit
| Prod "'x logic_term" "'x logic_term"
| FstL "'x logic_term"
| SndL "'x logic_term"
| Abs string logic_type "'x logic_term"
| AppL "'x logic_term" "'x logic_term" (infixl "$" 60)
| Const 'x
| Core "'x logic_term"
| Comp "'x logic_term" "'x logic_term"
| FalseTrm
| TrueTrm
| EqTrm logic_type "'x logic_term" "'x logic_term"
| Impl "'x logic_term" "'x logic_term"
| Conj "'x logic_term" "'x logic_term"
| Disj "'x logic_term" "'x logic_term"
| Sep "'x logic_term" "'x logic_term"
| Wand "'x logic_term" "'x logic_term"
| Guarded string logic_type "'x logic_term"
| Exists string logic_type "'x logic_term"
| Forall string logic_type "'x logic_term"
| Own "'x logic_term"
| Valid "'x logic_term"
| Persistent "'x logic_term"
| Plain "'x logic_term"
| Later "'x logic_term"
| Upd "'x logic_term"

definition wp :: "'x::ucamera logic_term" where
  "wp \<equiv> Abs ''e1'' Expr (Forall ''s1'' State (Forall ''k'' (List Observation) (Forall ''e2'' Expr
    (Forall ''s2'' State (Forall ''efs'' (List Expr) 
      (VarL ''head_step'' $ VarL ''e1'' $ VarL ''s1'' $ VarL ''k'' $ VarL ''e2'' $ VarL ''s2'' $ VarL ''efs''))))))"

(* Concurrent variable-for-variable substitution in logic terms *)
fun var_subst :: "(string \<Rightarrow> string) \<Rightarrow> 'x::ucamera logic_term \<Rightarrow> 'x logic_term" where
  "var_subst f (VarL x) = VarL (f x)"
| "var_subst f (Prod x y) = Prod (var_subst f x) (var_subst f y)"
| "var_subst f (FstL t) = FstL (var_subst f t)"
| "var_subst f (SndL t) = SndL (var_subst f t)"
| "var_subst f (Abs x \<tau> t) = Abs x \<tau> (var_subst (f(x:=x)) t)"
| "var_subst f (AppL t1 t2) = AppL (var_subst f t1) (var_subst f t2)"
| "var_subst f (Core t) = Core (var_subst f t)"
| "var_subst f (Comp t1 t2) = Comp (var_subst f t1) (var_subst f t2)"
| "var_subst f (EqTrm \<tau> t1 t2) = EqTrm \<tau> (var_subst f t1) (var_subst f t2)"
| "var_subst f (Impl t1 t2) = Impl (var_subst f t1) (var_subst f t2)"
| "var_subst f (Conj t1 t2) = Conj (var_subst f t1) (var_subst f t2)"
| "var_subst f (Disj t1 t2) = Disj (var_subst f t1) (var_subst f t2)"
| "var_subst f (Sep t1 t2) = Sep (var_subst f t1) (var_subst f t2)"
| "var_subst f (Wand t1 t2) = Wand (var_subst f t1) (var_subst f t2)"
| "var_subst f (Guarded x \<tau> t) = Guarded x \<tau> (var_subst (f(x:=x)) t)"
| "var_subst f (Exists x \<tau> t) = Exists x \<tau> (var_subst (f(x:=x)) t)"
| "var_subst f (Forall x \<tau> t) = Forall x \<tau> (var_subst (f(x:=x)) t)"
| "var_subst f (Own t) = Own (var_subst f t)"
| "var_subst f (Valid t) = Valid (var_subst f t)"
| "var_subst f (Persistent t) = Persistent (var_subst f t)"
| "var_subst f (Plain t) = Plain (var_subst f t)"
| "var_subst f (Later t) = Later (var_subst f t)"
| "var_subst f (Upd t) = Upd (var_subst f t)"
| "var_subst _ t = t"

(* Variable substitution with terms in logic terms *)
fun term_subst :: "'x::ucamera logic_term \<Rightarrow> string \<Rightarrow> 'x logic_term \<Rightarrow> 'x logic_term" where
  "term_subst f v (VarL x) = (if v=x then f else VarL x)"
| "term_subst f v (Prod x y) = Prod (term_subst f v x) (term_subst f v y)"
| "term_subst f v (FstL t) = FstL (term_subst f v t)"
| "term_subst f v (SndL t) = SndL (term_subst f v t)"
| "term_subst f v (Abs x \<tau> t) = Abs x \<tau> (if v=x then t else term_subst f v t)"
| "term_subst f v (AppL t1 t2) = AppL (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Core t) = Core (term_subst f v t)"
| "term_subst f v (Comp t1 t2) = Comp (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (EqTrm \<tau> t1 t2) = EqTrm \<tau> (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Impl t1 t2) = Impl (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Conj t1 t2) = Conj (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Disj t1 t2) = Disj (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Sep t1 t2) = Sep (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Wand t1 t2) = Wand (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Guarded x \<tau> t) = Guarded x \<tau> (if v=x then t else term_subst f v t)"
| "term_subst f v (Exists x \<tau> t) = Exists x \<tau> (if v=x then t else term_subst f v t)"
| "term_subst f v (Forall x \<tau> t) = Forall x \<tau> (if v=x then t else term_subst f v t)"
| "term_subst f v (Own t) = Own (term_subst f v t)"
| "term_subst f v (Valid t) = Valid (term_subst f v t)"
| "term_subst f v (Persistent t) = Persistent (term_subst f v t)"
| "term_subst f v (Plain t) = Plain (term_subst f v t)"
| "term_subst f v (Later t) = Later (term_subst f v t)"
| "term_subst f v (Upd t) = Upd (term_subst f v t)"
| "term_subst _ _ t = t"

(* The variable x can only appear under the later modality. *)
fun guarded :: "string \<Rightarrow> 'x::ucamera logic_term \<Rightarrow> bool" where
  "guarded _ (Later (VarL _)) = True"
| "guarded x (Prod t1 t2) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (FstL t) = guarded x t"
| "guarded x (SndL t) = guarded x t"
| "guarded x (Abs y _ t) = ((x=y) \<or> guarded x t)"
| "guarded x (Core t) = guarded x t"
| "guarded x (Comp t1 t2) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (EqTrm _ t1 t2) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (Impl t1 t2) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (Conj t1 t2) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (Disj t1 t2) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (Sep t1 t2) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (Wand t1 t2) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (Guarded y _ t) = ((x=y) \<or> guarded x t)"
| "guarded x (Exists y _ t) = ((x=y) \<or> guarded x t)"
| "guarded x (Forall y _ t) = ((x=y) \<or> guarded x t)"
| "guarded x (Own t) = guarded x t"
| "guarded x (Valid t) = guarded x t"
| "guarded x (Persistent t) = guarded x t"
| "guarded x (Plain t) = guarded x t"
| "guarded x (Later t) = guarded x t"
| "guarded x (Upd t) = guarded x t"
| "guarded _ (VarL _) = False"
| "guarded _ _ = True"

end