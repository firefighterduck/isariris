theory BaseLogicDeep1
imports CoreStructures "../HeapLang/PrimitiveLaws" "../HeapLang/State" "Nominal2.Nominal2" 
begin

subsection \<open>Uniform predicates as a deeply embedded formalization\<close>

datatype 'x ucamera_term =
  Var string
| Const 'x
| App "'x ucamera_term" "'x ucamera_term" (infixl "$" 60)
| Abs string "'x ucamera_term"

type_synonym 'x uterm = "'x ucamera_term"

datatype 'x::ucamera upred = 
  Pure "bool uterm"
| Conj "'x upred" "'x upred"
| Disj "'x upred" "'x upred"
| Forall string "'x upred"
| Exists string "'x upred"
| Sep "'x upred" "'x upred"
| Wand "'x upred" "'x upred"
| OwnU "'x uterm"
| Valid "'x uterm"
| Persistent "'x upred"
| Plain "'x upred"
| Later "'x upred"
| BUpd "'x upred"

abbreviation head_step_term :: "'a uterm \<Rightarrow> 'a uterm \<Rightarrow> 'a uterm \<Rightarrow> 'a uterm \<Rightarrow> 'a uterm \<Rightarrow> 'a uterm \<Rightarrow> 'a uterm" where
  "head_step_term e \<sigma> \<kappa> e2 \<sigma>2 efs \<equiv> (Var ''head_step'')$e$\<sigma>$\<kappa>$e2$\<sigma>2$efs"

text \<open>
  The above deep emebedding is not expressive enough.
  The following is a real example from the notion of WP and should be expressible in upred.
  The first definition is the syntax we want to achieve (minus syntactic sugar).
\<close>
abbreviation "wp \<equiv>
  (Forall ''s'' (Forall ''k'' (Forall ''e2'' (Forall ''s2'' (Forall ''efs'' 
    (Wand 
      (Pure (head_step_term (Var ''e'') (Var ''s'') (Var ''k'') (Var ''e2'') (Var ''s2'') (Var ''efs'')))
      (OwnU (Var ''own_state_heap''$Var ''s2''))
))))))"


axiomatization own_state_heap :: "state \<Rightarrow> heap_lang_heap"

text \<open>
  This second definition is the expected semantics of the partial WP term from above.
  The tricky question here is to find a function that can map the syntax above to the semantic below.
\<close>
definition "wp_sem e x n \<equiv> \<comment> \<open>Semantics as function type upred\<close>
  (\<forall>\<sigma> \<kappa> e2 \<sigma>2 efs y m. \<comment> \<open>Forall upred semantics\<close>
    m\<le>n \<longrightarrow> n_valid (x\<cdot>y) m \<longrightarrow> \<comment> \<open>Wand semantics\<close>
      (e \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs) \<longrightarrow> \<comment> \<open>head_step Pure semantics\<close>
      n_incl m (own_state_heap \<sigma>2) (x\<cdot>y))" \<comment> \<open>Own semantics\<close>

ML_file\<open>DeepSemantics.ml\<close>

setup \<open>
  register_sem \<^term>\<open>''head_step''\<close> \<^term>\<open>head_step\<close> #>
  register_sem \<^term>\<open>''own_state_heap''\<close> \<^term>\<open>own_state_heap\<close> #>
  register_sem \<^term>\<open>''e''\<close> \<^term>\<open>e::expr\<close> #>
  print_sem \<^term>\<open>wp\<close> ["\<sigma>", "\<kappa>", "e2", "\<sigma>2", "efs"] (SOME \<^typ>\<open>heap_lang_heap\<close>)
\<close>

(*
(* Concurrent variable-for-variable substitution in logic terms *)
fun var_subst_term :: "(string \<Rightarrow> string) \<Rightarrow> 'x ucamera_term \<Rightarrow> 'x ucamera_term" where
  "var_subst_term f (Var v) = Var (f v)"
| "var_subst_term f (Const c) = Const c"
| "var_subst_term f (App t r) = App (var_subst_term f t) (var_subst_term f r)"
| "var_subst_term f (Abs x b) = Abs x (var_subst_term (f(x:=x)) b)"

fun var_subst :: "(string \<Rightarrow> string) \<Rightarrow> 'x::ucamera upred \<Rightarrow> 'x upred" where
  "var_subst f (Conj t1 t2) = Conj (var_subst f t1) (var_subst f t2)"
| "var_subst f (Disj t1 t2) = Disj (var_subst f t1) (var_subst f t2)"
| "var_subst f (Sep t1 t2) = Sep (var_subst f t1) (var_subst f t2)"
| "var_subst f (Wand t1 t2) = Wand (var_subst f t1) (var_subst f t2)"
| "var_subst f (Exists x t) = Exists x (var_subst (f(x:=x)) t)"
| "var_subst f (Forall x t) = Forall x (var_subst (f(x:=x)) t)"
| "var_subst f (Persistent t) = Persistent (var_subst f t)"
| "var_subst f (Plain t) = Plain (var_subst f t)"
| "var_subst f (Later t) = Later (var_subst f t)"
| "var_subst f (BUpd t) = BUpd (var_subst f t)"
| "var_subst f (Pure bt) = Pure (var_subst_term f bt)"
| "var_subst f (Own t) = Own (var_subst_term f t)"
| "var_subst f (Valid t) = Valid (var_subst_term f t)"

(* Variable substitution with terms in logic terms *)
fun term_subst_term :: "'x ucamera_term \<Rightarrow> string \<Rightarrow> 'x ucamera_term \<Rightarrow> 'x ucamera_term" where
  "term_subst_term t v (Var x) = (if v=x then t else Var v)"
| "term_subst_term t v (Const c) = Const c"
| "term_subst_term t v (App t' r) = App (term_subst_term t v t') (term_subst_term t v r)"
| "term_subst_term t v (Abs x b) = Abs x (if x=v then b else term_subst_term t v b)"
  
fun term_subst :: "'x::ucamera ucamera_term \<Rightarrow> string \<Rightarrow> 'x upred \<Rightarrow> 'x upred" where
  "term_subst f v (Conj t1 t2) = Conj (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Disj t1 t2) = Disj (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Sep t1 t2) = Sep (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Wand t1 t2) = Wand (term_subst f v t1) (term_subst f v t2)"
| "term_subst f v (Exists x t) = Exists x (if v=x then t else term_subst f v t)"
| "term_subst f v (Forall x t) = Forall x (if v=x then t else term_subst f v t)"
| "term_subst f v (Persistent t) = Persistent (term_subst f v t)"
| "term_subst f v (Plain t) = Plain (term_subst f v t)"
| "term_subst f v (Later t) = Later (term_subst f v t)"
| "term_subst f v (BUpd t) = BUpd (term_subst f v t)"
| "term_subst f v (Pure t) = Pure (term_subst_term f v t)"
 
fun beta :: "'x::ucamera ucamera_term \<Rightarrow> 'x ucamera_term" where
  "beta (App (Abs x b) t) = term_subst_term (beta t) x (beta b)"
| "beta (Var v) = Var v"
| "beta (Const c) = Const c"
| "beta (Abs x b) = Abs x (beta b)"
| "beta (App t r) = App (beta t) (beta r)" *)

end