theory BaseLogicDeep
imports CoreStructures LogicSyntaxDeep
begin

section \<open> Base Logic \<close>
text \<open> The axiomatized and simplified Iris base logic_term \<close>

inductive well_typed :: "(string\<times>logic_type) list \<Rightarrow> 'a::ucamera logic_term \<Rightarrow> logic_type \<Rightarrow> bool" 
  ("_\<turnstile>_:_" 60) where
  ReflT: "[(x,\<tau>)] \<turnstile> Var x:\<tau>"
| WeakenT: "\<Gamma>\<turnstile>t:\<tau> \<Longrightarrow> (x,\<tau>')#\<Gamma>\<turnstile>t:\<tau>"
| SubstT: "(y,\<tau>')#(x,\<tau>')#\<Gamma>\<turnstile>t:\<tau> \<Longrightarrow> (x,\<tau>')#\<Gamma>\<turnstile>(var_subst (id(y:=x)) t):\<tau>"
| SwitchT: "\<Gamma>2@(x,\<tau>1)#(y,\<tau>2)#\<Gamma>1\<turnstile>t:\<tau> \<Longrightarrow> \<Gamma>2@(x,\<tau>2)#(y,\<tau>1)#\<Gamma>1\<turnstile>(var_subst (id(y:=x,x:=y)) t):\<tau>"
| UnitT: "\<Gamma>\<turnstile>Unit:UnitT"
| ProdT: "\<lbrakk>\<Gamma>\<turnstile>t:\<tau>1;\<Gamma>\<turnstile>u:\<tau>2\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Prod(t,u):ProdT(\<tau>1,\<tau>2)"
| FstT: "\<Gamma>\<turnstile>t:ProdT(\<tau>,\<tau>') \<Longrightarrow> \<Gamma>\<turnstile>Fst t:\<tau>"
| SndT: "\<Gamma>\<turnstile>t:ProdT(\<tau>',\<tau>) \<Longrightarrow> \<Gamma>\<turnstile>Snd t:\<tau>"
| LeftT: "\<Gamma>\<turnstile>t:\<tau> \<Longrightarrow> \<Gamma>\<turnstile>Left t:SumT \<tau> \<tau>'"
| RightT: "\<Gamma>\<turnstile>t:\<tau> \<Longrightarrow> \<Gamma>\<turnstile>Right t:SumT \<tau>' \<tau>"
| MatchT: "\<lbrakk>\<Gamma>\<turnstile>t:SumT \<tau>1 \<tau>2;(x,\<tau>1)#\<Gamma>\<turnstile>t1:\<tau>;(y,\<tau>2)#\<Gamma>\<turnstile>t2:\<tau>\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Match t x t1 y t2:\<tau>"
| AbsT: "(x,\<tau>)#\<Gamma>\<turnstile>t:\<tau>' \<Longrightarrow> \<Gamma>\<turnstile>Abs x \<tau> t:FunT \<tau> \<tau>'"
| AppT: "\<lbrakk>\<Gamma>\<turnstile>t:FunT \<tau> \<tau>';\<Gamma>\<turnstile>u:\<tau>\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>App t u:\<tau>'"
| ConstT: "\<Gamma>\<turnstile>Const a:M"
| CoreT: "\<Gamma>\<turnstile>a:M \<Longrightarrow> \<Gamma>\<turnstile>Core a:M"
| CompT: "\<lbrakk>\<Gamma>\<turnstile>a:M;\<Gamma>\<turnstile>b:M\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Comp a b:M"
| FalseT: "\<Gamma>\<turnstile>FalseTrm:PropT"
| TrueT: "\<Gamma>\<turnstile>TrueTrm:PropT"
| EqT: "\<lbrakk>\<Gamma>\<turnstile>t:\<tau>;\<Gamma>\<turnstile>u:\<tau>\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>EqTrm \<tau> t u:PropT"
| ImplT: "\<lbrakk>\<Gamma>\<turnstile>P:PropT;\<Gamma>\<turnstile>Q:PropT\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Impl P Q:PropT"
| ConjT: "\<lbrakk>\<Gamma>\<turnstile>P:PropT;\<Gamma>\<turnstile>Q:PropT\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Conj P Q:PropT"
| DisjT: "\<lbrakk>\<Gamma>\<turnstile>P:PropT;\<Gamma>\<turnstile>Q:PropT\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Disj P Q:PropT"
| SepT: "\<lbrakk>\<Gamma>\<turnstile>P:PropT;\<Gamma>\<turnstile>Q:PropT\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Sep P Q:PropT"
| WandT: "\<lbrakk>\<Gamma>\<turnstile>P:PropT;\<Gamma>\<turnstile>Q:PropT\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Wand P Q:PropT"
(* \<tau> also needs to be complete and inhabited but I have no idea how to formalize this. *)
| GuardedT: "\<lbrakk>guarded x t;(x,\<tau>)#\<Gamma>\<turnstile>t:\<tau>\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Guarded x \<tau> t:\<tau>"
| ExistsT: "(x,\<tau>)#\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Exists x \<tau> P:PropT"
| ForallT: "(x,\<tau>)#\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Forall x \<tau> P:PropT"
| OwnT: "\<Gamma>\<turnstile>a:M \<Longrightarrow> \<Gamma>\<turnstile>Own a:PropT"
(* Due to this predicate being defined inside base_logic, M is a camera. *)
| ValidT: "\<Gamma>\<turnstile>a:M \<Longrightarrow> \<Gamma>\<turnstile>Valid a:PropT"
| PersistentT: "\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Persistent P:PropT"
| PlainT: "\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Plain P:PropT"
| LaterT: "\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Later P:PropT"
| UpdT: "\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Upd P:PropT"

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
| EtaRed: "I|P\<turnstile>Q \<Longrightarrow> I|P\<turnstile>Abs x \<tau> (App Q (Var x))"

end