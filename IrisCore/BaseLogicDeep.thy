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
  | SumS "'a semantic_type + 'a semantic_type" | ProdT "'a semantic_type\<times>'a semantic_type" 
  | FunT "'a semantic_type fset"
  | Expr expr | State state | Observation observation | List "'a semantic_type list"

fun logic_semantic :: "'a::ucamera logic_term \<Rightarrow> 'a semantic_type" where
  "logic_semantic Unit = UnitS ()"
end