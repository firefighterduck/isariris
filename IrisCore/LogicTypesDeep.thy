theory LogicTypesDeep
imports LogicSyntaxDeep
begin

inductive well_typed :: "(string\<times>logic_type) list \<Rightarrow> 'a::ucamera logic_term \<Rightarrow> logic_type \<Rightarrow> bool" 
  ("_\<turnstile>_:_" 60) where
  ReflT: "[(x,\<tau>)] \<turnstile> VarL x:\<tau>"
| WeakenT: "\<Gamma>\<turnstile>t:\<tau> \<Longrightarrow> (x,\<tau>')#\<Gamma>\<turnstile>t:\<tau>"
| SubstT: "(y,\<tau>')#(x,\<tau>')#\<Gamma>\<turnstile>t:\<tau> \<Longrightarrow> (x,\<tau>')#\<Gamma>\<turnstile>(var_subst (id(y:=x)) t):\<tau>"
| SwitchT: "\<Gamma>2@(x,\<tau>1)#(y,\<tau>2)#\<Gamma>1\<turnstile>t:\<tau> \<Longrightarrow> \<Gamma>2@(x,\<tau>2)#(y,\<tau>1)#\<Gamma>1\<turnstile>(var_subst (id(y:=x,x:=y)) t):\<tau>"
| UnitT: "\<Gamma>\<turnstile>Unit:UnitT"
| ProdT: "\<lbrakk>\<Gamma>\<turnstile>t:\<tau>1;\<Gamma>\<turnstile>u:\<tau>2\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Prod t u:ProdT \<tau>1 \<tau>2"
| FstT: "\<Gamma>\<turnstile>t:ProdT \<tau> \<tau>' \<Longrightarrow> \<Gamma>\<turnstile>FstL t:\<tau>"
| SndT: "\<Gamma>\<turnstile>t:ProdT \<tau>' \<tau> \<Longrightarrow> \<Gamma>\<turnstile>SndL t:\<tau>"
| AbsT: "(x,\<tau>)#\<Gamma>\<turnstile>t:\<tau>' \<Longrightarrow> \<Gamma>\<turnstile>Abs x \<tau> t:FunT \<tau> \<tau>'"
| AppT: "\<lbrakk>\<Gamma>\<turnstile>t:FunT \<tau> \<tau>';\<Gamma>\<turnstile>u:\<tau>\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>AppL t u:\<tau>'"
| ConstT: "\<Gamma>\<turnstile>Const a:CmraT"
| CoreT: "\<Gamma>\<turnstile>a:CmraT \<Longrightarrow> \<Gamma>\<turnstile>Core a:CmraT"
| CompT: "\<lbrakk>\<Gamma>\<turnstile>a:CmraT;\<Gamma>\<turnstile>b:CmraT\<rbrakk> \<Longrightarrow> \<Gamma>\<turnstile>Comp a b:CmraT"
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
| OwnT: "\<Gamma>\<turnstile>a:CmraT \<Longrightarrow> \<Gamma>\<turnstile>Own a:PropT"
| ValidT: "\<Gamma>\<turnstile>a:CmraT \<Longrightarrow> \<Gamma>\<turnstile>Valid a:PropT"
| PersistentT: "\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Persistent P:PropT"
| PlainT: "\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Plain P:PropT"
| LaterT: "\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Later P:PropT"
| UpdT: "\<Gamma>\<turnstile>P:PropT \<Longrightarrow> \<Gamma>\<turnstile>Upd P:PropT"

fun comb_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b option" where
  "comb_option (Some x) (Some y) f = Some (f x y)"
| "comb_option _ _ _ = None"

fun comb_option_eq :: "'a \<Rightarrow> 'a option \<Rightarrow> 'b \<Rightarrow> 'b option" where
  "comb_option_eq e (Some x) C = (if x=e then Some C else None)"
| "comb_option_eq _ _ _ = None"

fun comb_option_eq2 :: "'a \<Rightarrow>'a option \<Rightarrow> 'a option \<Rightarrow> 'b \<Rightarrow> 'b option" where
  "comb_option_eq2 e (Some x) (Some y) C = (if x=e\<and> y=e then Some C else None)"
| "comb_option_eq2 _ _ _ _ = None"

fun type_of_term :: "'a::ucamera logic_term \<Rightarrow> (string\<rightharpoonup>logic_type) \<Rightarrow> logic_type option" where
  "type_of_term Unit _ = Some UnitT"
| "type_of_term (VarL s) \<Gamma> = \<Gamma> s"
| "type_of_term (Prod f s) \<Gamma> = comb_option (type_of_term f \<Gamma>) (type_of_term s \<Gamma>) ProdT"
| "type_of_term (FstL p) \<Gamma> = 
  (case type_of_term p \<Gamma> of Some (ProdT fT _) \<Rightarrow> Some fT | _ \<Rightarrow> None)"
| "type_of_term (SndL p) \<Gamma> =
  (case type_of_term p \<Gamma> of Some (ProdT _ sT) \<Rightarrow> Some sT | _ \<Rightarrow> None)"
| "type_of_term (Abs v vT b) \<Gamma> = map_option (\<lambda>bT. FunT vT bT) (type_of_term b (\<Gamma>(v \<mapsto> vT)))"
| "type_of_term (AppL f x) \<Gamma> = (case (type_of_term f \<Gamma>) of Some (FunT pT rT) \<Rightarrow> 
    (case (type_of_term x \<Gamma>) of Some xT \<Rightarrow> (if xT=pT then Some rT else None) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "type_of_term (Const _) _ = Some CmraT"
| "type_of_term (Core x) \<Gamma> = (case type_of_term x \<Gamma> of Some CmraT \<Rightarrow> Some CmraT | _ \<Rightarrow> None)"
| "type_of_term (Comp x y) \<Gamma> = comb_option_eq2 CmraT (type_of_term x \<Gamma>) (type_of_term y \<Gamma>) CmraT"
| "type_of_term FalseTrm _ = Some PropT"
| "type_of_term TrueTrm _ = Some PropT"
| "type_of_term (EqTrm \<tau> x y) \<Gamma> = comb_option_eq2 \<tau> (type_of_term x \<Gamma>) (type_of_term y \<Gamma>) PropT"
| "type_of_term (Impl P Q) \<Gamma> = comb_option_eq2 PropT (type_of_term P \<Gamma>) (type_of_term Q \<Gamma>) PropT"
| "type_of_term (Conj P Q) \<Gamma> = comb_option_eq2 PropT (type_of_term P \<Gamma>) (type_of_term Q \<Gamma>) PropT"
| "type_of_term (Disj P Q) \<Gamma> = comb_option_eq2 PropT (type_of_term P \<Gamma>) (type_of_term Q \<Gamma>) PropT"
| "type_of_term (Sep P Q) \<Gamma> = comb_option_eq2 PropT (type_of_term P \<Gamma>) (type_of_term Q \<Gamma>) PropT"
| "type_of_term (Wand P Q) \<Gamma> = comb_option_eq2 PropT (type_of_term P \<Gamma>) (type_of_term Q \<Gamma>) PropT"
| "type_of_term (Guarded v vT b) \<Gamma> = (if guarded v b then 
  Option.bind (type_of_term b (\<Gamma>(v\<mapsto>vT))) (\<lambda>bT. if bT=vT then Some vT else None) else None)"
| "type_of_term (Exists v vT b) \<Gamma> = comb_option_eq PropT (type_of_term b (\<Gamma>(v\<mapsto>vT))) PropT"
| "type_of_term (Forall v vT b) \<Gamma> = comb_option_eq PropT (type_of_term b (\<Gamma>(v\<mapsto>vT))) PropT"
| "type_of_term (Own x) \<Gamma> = comb_option_eq CmraT (type_of_term x \<Gamma>) PropT"
| "type_of_term (Valid x) \<Gamma> = comb_option_eq CmraT (type_of_term x \<Gamma>) PropT"
| "type_of_term (Persistent x) \<Gamma> = comb_option_eq PropT (type_of_term x \<Gamma>) PropT"
| "type_of_term (Plain x) \<Gamma> = comb_option_eq PropT (type_of_term x \<Gamma>) PropT"
| "type_of_term (Later x) \<Gamma> = comb_option_eq PropT (type_of_term x \<Gamma>) PropT"
| "type_of_term (Upd x) \<Gamma> = comb_option_eq PropT (type_of_term x \<Gamma>) PropT"

lemma "(type_of_term t (map_of \<Gamma>) = Some \<tau>) \<longleftrightarrow> \<Gamma>\<turnstile>t:\<tau>"
sorry

definition head_step_ty :: logic_type where
  "head_step_ty \<equiv> Expr \<rightarrow> State \<rightarrow> (List Observation) \<rightarrow> Expr \<rightarrow> State \<rightarrow> (List Expr) \<rightarrow> PropT"

lemma "type_of_term wp [''head_step''\<mapsto>head_step_ty] = Some (Expr \<rightarrow> PropT)"
  by (simp add: wp_def head_step_ty_def)
end