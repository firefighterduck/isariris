theory LogicSyntax
imports Main
begin
(* The Coq formalization also used the empty type but I have no idea why 
  or whether HOL has such a type. M is the carrier type of the underlying camera. *)
datatype logic_type = PropT | M |EmptyT | UnitT | SumT logic_type logic_type
  | ProdT "logic_type\<times>logic_type" | FunT logic_type logic_type

datatype 'x logic_term = 
  Var string
| Abort "'x logic_term"
| Unit
| Prod "'x logic_term\<times>'x logic_term"
| Fst "'x logic_term"
| Snd "'x logic_term"
| Abs string logic_type "'x logic_term"
| App "'x logic_term" "'x logic_term"
| Left "'x logic_term"
| Right "'x logic_term"
| Match "'x logic_term" string "'x logic_term" string "'x logic_term"
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

(* Concurrent variable-for-variable substitution in logic terms *)
fun var_subst :: "(string \<Rightarrow> string) \<Rightarrow> 'x logic_term \<Rightarrow> 'x logic_term" where
  "var_subst f (Var x) = Var (f x)"
| "var_subst f (Prod (x,y)) = Prod (var_subst f x, var_subst f y)"
| "var_subst f (Fst t) = Fst (var_subst f t)"
| "var_subst f (Snd t) = Snd (var_subst f t)"
| "var_subst f (Abs x \<tau> t) = Abs x \<tau> (var_subst (f(x:=x)) t)"
| "var_subst f (App t1 t2) = App (var_subst f t1) (var_subst f t2)"
| "var_subst f (Left t) = Left (var_subst f t)"
| "var_subst f (Right t) = Right (var_subst f t)"
| "var_subst f (Match t x l y r) = 
  Match (var_subst f t) x (var_subst (f(x:=x)) l) y (var_subst (f(y:=y)) r)"
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
fun term_subst :: "'x logic_term \<Rightarrow> string \<Rightarrow> 'x logic_term \<Rightarrow> 'x logic_term" where
  "term_subst f v (Var x) = (if v=x then f else Var x)"
| "term_subst f v (Prod (x,y)) = Prod (term_subst f v x, term_subst f v y)"
| "term_subst f v (Fst t) = Fst (term_subst f v t)"
| "term_subst f v (Snd t) = Snd (term_subst f v t)"
| "term_subst f v (Abs x \<tau> t) = Abs x \<tau> (if v=x then t else term_subst f v t)"
| "term_subst f v (App t1 t2) = App (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Left t) = Left (term_subst f v t)"
| "term_subst f v (Right t) = Right (term_subst f v t)"
| "term_subst f v (Match t x l y r) = 
  Match (term_subst f v t) x (if v=x then l else term_subst f v l) 
  y (if v=y then r else term_subst f v r)"
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
fun guarded :: "string \<Rightarrow> 'x logic_term \<Rightarrow> bool" where
  "guarded _ (Later (Var _)) = True"
| "guarded x (Abort t) = guarded x t"
| "guarded x (Prod (t1,t2)) = (guarded x t1 \<and> guarded x t2)"
| "guarded x (Fst t) = guarded x t"
| "guarded x (Snd t) = guarded x t"
| "guarded x (Abs y _ t) = ((x=y) \<or> guarded x t)"
| "guarded x (Left t) = guarded x t"
| "guarded x (Right t) = guarded x t"
| "guarded x (Match t y l z r) = (guarded x t \<and> ((x=y) \<or> guarded x l) \<and> ((x=z) \<or> guarded x r))"
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
| "guarded _ (Var _) = False"
| "guarded _ _ = True"

end