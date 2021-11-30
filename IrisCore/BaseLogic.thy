theory BaseLogic
imports CoreStructures LogicSyntax
begin

section \<open> Base Logic \<close>
text \<open> The axiomatized and simplified Iris base logic_term \<close>

(* This would normally include a signature, but I have no idea how to formalize it. *)
(* It seems to me that the signature is also not explicitly stated in the Coq implementation. *)
locale base_logic =
  total_camera

context base_logic
begin
inductive well_typed :: "(string\<times>logic_type) list \<Rightarrow> 'a logic_term \<Rightarrow> logic_type \<Rightarrow> bool" 
  ("_\<turnstile>_:_" 60) where
  ReflT: "[(x,\<tau>)] \<turnstile> Var x:\<tau>"
| WeakenT: "\<Gamma>\<turnstile>t:\<tau> \<Longrightarrow> (x,\<tau>')#\<Gamma>\<turnstile>t:\<tau>"
| SubstT: "(y,\<tau>')#(x,\<tau>')#\<Gamma>\<turnstile>t:\<tau> \<Longrightarrow> (x,\<tau>')#\<Gamma>\<turnstile>(logic_subst (id(y:=x)) t):\<tau>"
| SwitchT: "\<Gamma>2@(x,\<tau>1)#(y,\<tau>2)#\<Gamma>1\<turnstile>t:\<tau> \<Longrightarrow> \<Gamma>2@(x,\<tau>2)#(y,\<tau>1)#\<Gamma>1\<turnstile>(logic_subst (id(y:=x,x:=y)) t):\<tau>"
| AbortT: "\<Gamma>\<turnstile>t:EmptyT \<Longrightarrow> \<Gamma>\<turnstile>Abort t:\<tau>"
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
end
end