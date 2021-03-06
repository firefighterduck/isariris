theory BaseLogicDeep
imports CoreStructures LogicSyntaxDeep "../HeapLang/State" LogicTypesDeep
begin

section \<open> Base Logic \<close>

(* Irrelevant contexts that were left out in the description are called I instead of \<Gamma>.  *)
inductive judgement :: "(string\<times>logic_type) list \<Rightarrow> 'a::ucamera logic_term \<Rightarrow> 'a logic_term \<Rightarrow> bool" 
  ("_ | _ \<turnstile> _" 60)  where
  Asm: "I|P\<turnstile>P"
| Cut: "\<lbrakk>I|P\<turnstile>Q; I|Q\<turnstile>R\<rbrakk> \<Longrightarrow> I|P\<turnstile>Q"
| Eq: "\<lbrakk>(x,\<tau>)#\<Gamma>\<turnstile>Q:PropT; \<Gamma>|P\<turnstile>term_subst t x Q; \<Gamma>|P\<turnstile>EqTrm \<tau> t t'\<rbrakk> \<Longrightarrow> \<Gamma>|P\<turnstile>term_subst t' x Q"
| Refl: "I|TrueTrm\<turnstile>EqTrm \<tau> t t"
| BotE: "I|FalseTrm\<turnstile>P"
| TopI: "I|P\<turnstile>TrueTrm"
| ConjI: "\<lbrakk>I|P\<turnstile>Q; I|P\<turnstile>R\<rbrakk> \<Longrightarrow> I|P\<turnstile>Conj Q R"
| ConjEL: "I|P\<turnstile>Conj Q R \<Longrightarrow> I|P\<turnstile>Q"
| ConjER: "I|P\<turnstile>Conj Q R \<Longrightarrow> I|P\<turnstile>R"
| DisjIL: "I|P\<turnstile>Q \<Longrightarrow> I|P\<turnstile>Disj Q R"
| DisjIR: "I|P\<turnstile>R \<Longrightarrow> I|P\<turnstile>Disj Q R"
| DisjE: "\<lbrakk>I|P\<turnstile>R; I|Q\<turnstile>R\<rbrakk> \<Longrightarrow> I|Disj P Q\<turnstile>R"
| ImplI: "I|Conj P Q\<turnstile>R \<Longrightarrow> I|P\<turnstile>Impl Q R"
| ImplE: "\<lbrakk>I|P\<turnstile>Impl Q R; I|P\<turnstile>Q\<rbrakk> \<Longrightarrow> I|P\<turnstile>R"
| ForallI: "(x,\<tau>)#\<Gamma>|P\<turnstile>Q \<Longrightarrow> \<Gamma>|P\<turnstile>Forall x \<tau> Q"
| ForallE: "\<lbrakk>\<Gamma>|P\<turnstile>Forall x \<tau> Q; \<Gamma>\<turnstile>t:\<tau>\<rbrakk> \<Longrightarrow> \<Gamma>|P\<turnstile>term_subst t x Q"
| ExistsI: "\<lbrakk>\<Gamma>|P\<turnstile>term_subst t x Q; \<Gamma>\<turnstile>t:\<tau>\<rbrakk> \<Longrightarrow> \<Gamma>|P\<turnstile>Exists x \<tau> Q"
| ExistsE: "(x,\<tau>)#\<Gamma>|P\<turnstile>Q \<Longrightarrow> \<Gamma>|Exists x \<tau> P\<turnstile>Q"
| EtaRed: "I|P\<turnstile>Q \<Longrightarrow> I|P\<turnstile>Abs x \<tau> (AppL Q (VarL x))"

datatype 'a semantic_type = PropS "'a \<Rightarrow> nat \<Rightarrow> bool" | CmraS 'a | UnitS unit 
  | ProdS "'a semantic_type\<times>'a semantic_type" 
  | FunS "('a semantic_type\<times>'a semantic_type) fset" \<comment> \<open>BNFs can't have recursion in function arguments\<close>
  | ExprS expr | StateS state | ObservationS observation | ListS "'a semantic_type list"
  
definition funS :: "('a semantic_type\<Rightarrow>'a semantic_type) \<Rightarrow> 'a semantic_type" where
  "funS f = FunS (Abs_fset {(x,y) | x y. f x = y})"

definition appS :: "'a semantic_type \<Rightarrow> 'a semantic_type \<Rightarrow> 'a semantic_type" where
  "appS fS x \<equiv> case fS of FunS f \<Rightarrow> the_elem ((fset f) `` {x}) | _ \<Rightarrow> undefined"
notation appS (infixl "$$" 60)

abbreviation "unwrap_expr eS \<equiv> case eS of ExprS e \<Rightarrow> e | _ \<Rightarrow> undefined"
abbreviation "unwrap_state sS \<equiv> case sS of StateS s \<Rightarrow> s | _ \<Rightarrow> undefined"
abbreviation "unwrap_obs oS \<equiv> case oS of ObservationS ob \<Rightarrow> ob | _ \<Rightarrow> undefined"
abbreviation "unwrap_list m lS \<equiv> case lS of ListS l \<Rightarrow> map m l | _ \<Rightarrow> undefined"
abbreviation "unwrap_prop pS x n \<equiv> case pS of PropS p \<Rightarrow> p x n | _ \<Rightarrow> undefined"

definition head_step_sem :: "'a::ucamera semantic_type" where
  "head_step_sem \<equiv> funS (\<lambda>e1S. funS (\<lambda>s1S. funS (\<lambda>kl. funS (\<lambda>e2S. funS (\<lambda>s2S. funS (\<lambda>efsl. 
      PropS (\<lambda>_ _.
      ((unwrap_expr e1S) (unwrap_state s1S) (unwrap_list unwrap_obs kl) \<Rightarrow>\<^sub>h 
      (unwrap_expr e2S) (unwrap_state s2S) (unwrap_list unwrap_expr efsl))
  )))))))"
  
definition "wp_sem \<equiv> funS 
  (\<lambda>e. PropS (\<lambda>x n. \<forall>s1 k e2 s2 efs. unwrap_prop (head_step_sem$$e$$s1$$k$$e2$$s2$$efs) x n))"

abbreviation "comb_prop p q pcomb \<equiv> (case p of Some (PropS p') \<Rightarrow> (case q of Some (PropS q') \<Rightarrow> 
  Some (PropS (\<lambda>a n. pcomb p' q' a n)) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
  
fun logic_semantic 
  :: "'a::ucamera logic_term \<Rightarrow> (string\<rightharpoonup>'a semantic_type) \<Rightarrow> 'a semantic_type option" where
  "logic_semantic Unit _ = Some (UnitS ())"
| "logic_semantic (VarL v) \<Gamma> = \<Gamma> v"
| "logic_semantic (Prod f s) \<Gamma> = comb_option (logic_semantic f \<Gamma>) (logic_semantic s \<Gamma>) 
  (\<lambda>fS sS. ProdS (fS,sS))"
| "logic_semantic (FstL p) \<Gamma> = (case logic_semantic p \<Gamma> of Some (ProdS pS) \<Rightarrow> Some (fst pS) 
  | _ \<Rightarrow> None)"
| "logic_semantic (SndL p) \<Gamma> = (case logic_semantic p \<Gamma> of Some (ProdS pS) \<Rightarrow> Some (snd pS) 
  | _ \<Rightarrow> None)"
| "logic_semantic (Abs v _ b) \<Gamma> = Some (funS (\<lambda>vS. the (logic_semantic b (\<Gamma>(v\<mapsto>vS)))))"
| "logic_semantic (AppL f x) \<Gamma> = comb_option (logic_semantic f \<Gamma>) (logic_semantic x \<Gamma>) appS"
| "logic_semantic (Const x) _ = Some (CmraS x)"
| "logic_semantic (Core x) \<Gamma> = (case logic_semantic x \<Gamma> of Some (CmraS x') \<Rightarrow> Some (CmraS (core x')) 
  | _ \<Rightarrow> None)"
| "logic_semantic (Comp x y) \<Gamma> = (case logic_semantic x \<Gamma> of Some (CmraS x') \<Rightarrow> 
  (case logic_semantic y \<Gamma> of Some (CmraS y') \<Rightarrow> Some (CmraS (x'\<cdot>y')) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "logic_semantic FalseTrm _ = Some (PropS (\<lambda>_ _. False))"
| "logic_semantic TrueTrm _ = Some (PropS (\<lambda>_ _. True))"
| "logic_semantic (EqTrm _ x y) \<Gamma> = comb_option (logic_semantic x \<Gamma>) (logic_semantic y \<Gamma>) 
  (\<lambda>x y. PropS (\<lambda> _ _. x=y))"
| "logic_semantic (Impl p q) \<Gamma> = comb_prop (logic_semantic p \<Gamma>) (logic_semantic q \<Gamma>) 
  (\<lambda>p q a n. p a n \<longrightarrow> q a n)"
| "logic_semantic (Conj p q) \<Gamma> = comb_prop (logic_semantic p \<Gamma>) (logic_semantic q \<Gamma>) 
  (\<lambda>p q a n. p a n \<and> q a n)"
| "logic_semantic (Disj p q) \<Gamma> = comb_prop (logic_semantic p \<Gamma>) (logic_semantic q \<Gamma>) 
  (\<lambda>p q a n. p a n \<or> q a n)"
| "logic_semantic (Sep p q) \<Gamma> = comb_prop (logic_semantic p \<Gamma>) (logic_semantic q \<Gamma>) 
  (\<lambda>p q a n. \<exists>b1 b2. n_equiv n a (b1\<cdot>b2) \<and> p b1 n \<and> q b2 n)"
| "logic_semantic (Wand p q) \<Gamma> = comb_prop (logic_semantic p \<Gamma>) (logic_semantic q \<Gamma>) 
  (\<lambda>p q a n. \<forall>b m. m\<le>n \<longrightarrow> n_valid (a \<cdot> b) m \<longrightarrow> p b m \<longrightarrow> q (a \<cdot> b) m)"
| "logic_semantic (Guarded v _ b) \<Gamma> = (if guarded v b then 
  Some (funS (\<lambda>vS. the (logic_semantic b (\<Gamma>(v\<mapsto>vS))))) else None)"
| "logic_semantic (Exists v _ b) \<Gamma> = 
  Some (PropS (\<lambda>a n. \<exists>vS. unwrap_prop (the (logic_semantic b (\<Gamma>(v\<mapsto>vS)))) a n))"
| "logic_semantic (Forall v _ b) \<Gamma> = 
  Some (PropS (\<lambda>a n. \<forall>vS. unwrap_prop (the (logic_semantic b (\<Gamma>(v\<mapsto>vS)))) a n))"
| "logic_semantic (Own x) \<Gamma> = (case logic_semantic x \<Gamma> of Some (CmraS x') \<Rightarrow> 
  Some (PropS (\<lambda>a n. n_incl n x' a)) | _ \<Rightarrow> None)"
| "logic_semantic (Valid x) \<Gamma> = (case logic_semantic x \<Gamma> of Some (CmraS x') \<Rightarrow> 
  Some (PropS (\<lambda>_. n_valid x')) | _ \<Rightarrow> None)"
| "logic_semantic (Persistent p) \<Gamma> = (case logic_semantic p \<Gamma> of Some (PropS p') \<Rightarrow> 
  Some (PropS (\<lambda>a n. p' (core a) n)) | _ \<Rightarrow> None)"
| "logic_semantic (Plain p) \<Gamma> = (case logic_semantic p \<Gamma> of Some (PropS p') \<Rightarrow>
  Some (PropS (\<lambda>_ n. p' \<epsilon> n)) | _ \<Rightarrow> None)"
| "logic_semantic (Later p) \<Gamma> = (case logic_semantic p \<Gamma> of Some (PropS p') \<Rightarrow>
  Some (PropS (\<lambda>a n. n=0 \<or> p' a (n-1))))"
| "logic_semantic (Upd p) \<Gamma> = (case logic_semantic p \<Gamma> of Some (PropS p') \<Rightarrow>
  Some (PropS (\<lambda>a n. \<forall>m b. m\<le>n \<longrightarrow> n_valid (a \<cdot> b) m \<longrightarrow> (\<exists>c. n_valid (c \<cdot> b) m \<and> p' c m))))"

lemma "\<lbrakk>dom \<Gamma>S \<subseteq> dom \<Gamma>T; type_of_term t \<Gamma>T = None\<rbrakk> \<Longrightarrow> logic_semantic t \<Gamma>S = None"
apply (induction t)
apply (auto split: option.splits)
sorry

definition entails :: "'a::ucamera semantic_type \<Rightarrow> 'a semantic_type \<Rightarrow> bool" where
  "entails P Q \<equiv> let P' = unwrap_prop P in let Q' = unwrap_prop Q in 
    (\<forall>a n. n_valid a n \<longrightarrow> P' a n \<longrightarrow> Q' a n)"

lemma "\<lbrakk>\<Gamma>T|P\<turnstile>Q; logic_semantic P \<Gamma>S = Some P'; logic_semantic Q \<Gamma>S = Some Q'\<rbrakk> \<Longrightarrow> entails P' Q'"
sorry
    
lemma "logic_semantic wp [''head_step''\<mapsto>head_step_sem] = Some wp_sem"
apply (auto simp add: wp_def head_step_sem_def funS_def appS_def the_elem_def Abs_fset_inverse)
sorry


text \<open>
  Deep Embedding of uniform predicates:

  - all Iris logic formulae as instances of datatype \<^typ>\<open>'a logic_term\<close>
  - terms with camera objects (\<^typ>\<open>'a::ucamera\<close>/\<^const>\<open>CmraT\<close>) very simple: 
    \<^const>\<open>Const\<close>, \<^const>\<open>Core\<close>, \<^const>\<open>Comp\<close>
  - uniform predicates about camera objects (\<^typ>\<open>'a::ucamera\<Rightarrow>nat\<Rightarrow>bool\<close>/\<^const>\<open>PropT\<close>) very simple: 
    \<^const>\<open>Own\<close>, \<^const>\<open>Valid\<close>, \<^const>\<open>Conj\<close>, \<^const>\<open>Disj\<close>, \<^const>\<open>TrueTrm\<close>, \<^const>\<open>FalseTrm\<close>, 
    \<^const>\<open>EqTrm\<close>, \<^const>\<open>Impl\<close>, \<^const>\<open>Sep\<close>, \<^const>\<open>Wand\<close>, \<^const>\<open>Persistent\<close>, \<^const>\<open>Plain\<close>, 
    \<^const>\<open>Later\<close>, \<^const>\<open>Upd\<close>, (maybe also have a wrapper for "pure" propositions, e.g. \<open>\<lambda>a n. True\<close>)
  - BUT: Iris base logic also reasons about terms of other types as well:
    \<^typ>\<open>unit\<close>/\<^const>\<open>UnitT\<close>, \<^typ>\<open>'a\<times>'b\<close>/\<^const>\<open>ProdT\<close>, \<^typ>\<open>'a\<Rightarrow>'b\<close>/\<^const>\<open>FunT\<close> (i.e. \<^typ>\<open>'a-n>'b\<close>),
    \<^typ>\<open>'a+'b\<close> (omitted), and all other types an application needs (e.g. \<^typ>\<open>expr\<close>/\<^const>\<open>Expr\<close>,
    \<^typ>\<open>state\<close>/\<^const>\<open>State\<close>, \<^typ>\<open>observation\<close>/\<^const>\<open>Observation\<close> and lists of these types)
  - Do we need to be to argue about other types than cameras within the base logic?
    => if we would only be able to reason about cameras, we would lose the ability to have 
    sideconditions about them (e.g. if we can do a head step in HeapLang, we can also do a ghost update
    to then own the new state)
    => quantifiers make things really difficult either way if the variable, over which we abstract
    is used within a "pure" context
    => The biggest problem is the semantics of functions and application, no deep embedding can have 
    well-typed function semantics (i.e. a datatype which wraps functions on itself)
  - Make quantifiers only inside a Pure wrapper doesn't work as it cuts the connection of outer camera
    objects necessary for the semantics from the inner ones.
\<close>
end