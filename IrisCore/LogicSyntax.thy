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

(* Variable substitution in logic terms *)
fun logic_subst :: "(string \<Rightarrow> string) \<Rightarrow> 'x logic_term \<Rightarrow> 'x logic_term" where
  "logic_subst f (Var x) = Var (f x)"
| "logic_subst f (Prod (x,y)) = Prod (logic_subst f x, logic_subst f y)"
| "logic_subst f (Fst t) = Fst (logic_subst f t)"
| "logic_subst f (Snd t) = Snd (logic_subst f t)"
| "logic_subst f (Abs x \<tau> t) = Abs x \<tau> (logic_subst (f(x:=x)) t)"
| "logic_subst f (App t1 t2) = App (logic_subst f t1) (logic_subst f t2)"
| "logic_subst f (Left t) = Left (logic_subst f t)"
| "logic_subst f (Right t) = Right (logic_subst f t)"
| "logic_subst f (Match t x l y r) = 
  Match (logic_subst f t) x (logic_subst (f(x:=x)) l) y (logic_subst (f(y:=y)) r)"
| "logic_subst f (Core t) = Core (logic_subst f t)"
| "logic_subst f (Comp t1 t2) = Comp (logic_subst f t1) (logic_subst f t2)"
| "logic_subst f (EqTrm \<tau> t1 t2) = EqTrm \<tau> (logic_subst f t1) (logic_subst f t2)"
| "logic_subst f (Impl t1 t2) = Impl (logic_subst f t1) (logic_subst f t2)"
| "logic_subst f (Conj t1 t2) = Conj (logic_subst f t1) (logic_subst f t2)"
| "logic_subst f (Disj t1 t2) = Disj (logic_subst f t1) (logic_subst f t2)"
| "logic_subst f (Sep t1 t2) = Sep (logic_subst f t1) (logic_subst f t2)"
| "logic_subst f (Wand t1 t2) = Wand (logic_subst f t1) (logic_subst f t2)"
| "logic_subst f (Guarded x \<tau> t) = Guarded x \<tau> (logic_subst (f(x:=x)) t)"
| "logic_subst f (Exists x \<tau> t) = Exists x \<tau> (logic_subst (f(x:=x)) t)"
| "logic_subst f (Forall x \<tau> t) = Forall x \<tau> (logic_subst (f(x:=x)) t)"
| "logic_subst f (Own t) = Own (logic_subst f t)"
| "logic_subst f (Valid t) = Valid (logic_subst f t)"
| "logic_subst f (Persistent t) = Persistent (logic_subst f t)"
| "logic_subst f (Plain t) = Plain (logic_subst f t)"
| "logic_subst f (Later t) = Later (logic_subst f t)"
| "logic_subst f (Upd t) = Upd (logic_subst f t)"
| "logic_subst _ t = t"

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