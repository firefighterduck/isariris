theory HeapLang
imports 
  Main
  Locations
begin

section \<open> HeapLang Definition \<close>
text \<open> The basic language definition \<close>
text \<open> Based on https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lang.v\<close>

type_synonym proph_id = nat

(*
  Binder type for anonymous and named binders, 
  cf. https://gitlab.mpi-sws.org/iris/stdpp/-/blob/master/theories/binders.v 
*)
type_synonym binder_t = "string option" 

(* Literals *)
datatype base_lit =
  LitInt int | LitBool bool | LitUnit | LitPoison | LitLoc loc | LitProphecy proph_id

(* Unary operator symbols*)
datatype un_op =
  NegOp | MinusUnOp

(* Binary Operator Symbols *)
datatype bin_op =
  PlusOp | MinusOp | MultOp | QuotOp | RemOp | AndOp | OrOp | XorOp | ShiftLOp
  | ShiftROp | LeOp | LtOp | EqOp | OffsetOp

(* Expressions and values *)
datatype expr =
  (* Values *)
  Val val
  (* Base lambda calculus *)
  | Var string
  | Rec binder_t binder_t expr
  | App expr expr
  (* Base types and their operations *)
  | UnOp un_op expr
  | BinOp bin_op expr expr
  | If expr expr expr
  (* Products *)
  | Pair expr expr
  | Fst expr
  | Snd expr
  (* Sums *)
  | InjL expr
  | InjR expr
  | Case expr expr expr
  (* Concurrency *)
  | Fork expr
  (* Heap *)
  | AllocN expr expr (* array length (positive number), initial value *)
  | Free expr
  | Load expr
  | Store expr expr
  | CmpXchg expr expr expr (* Compare-exchange *)
  | Xchg expr expr (* exchange *)
  | FAA expr expr (* Fetch-and-add *)
  (* Prophecy *)
  | NewProph
  | Resolve expr expr expr (* wrapped expr, proph, val *)
and val =
  LitV base_lit
  | RecV binder_t binder_t expr
  | PairV val val
  | InjLV val
  | InjRV val
  
(* An observation associates a prophecy variable (identifier) to a pair of values. *)
type_synonym observation = "proph_id * val * val"

abbreviation "of_val \<equiv> Val"

fun to_val :: "expr \<Rightarrow> val option" where
  "to_val (Val v) = Some v"
| "to_val _ = None"

fun lit_is_unboxed :: "base_lit \<Rightarrow> bool" where
  "lit_is_unboxed (LitProphecy _) = False"
| "lit_is_unboxed LitPoison = False"
| "lit_is_unboxed _ = True"

fun val_is_unboxed :: "val \<Rightarrow> bool" where
  "val_is_unboxed (LitV l) = lit_is_unboxed l"
| "val_is_unboxed (InjLV (LitV l)) = lit_is_unboxed l"
| "val_is_unboxed (InjRV (LitV l)) = lit_is_unboxed l"
| "val_is_unboxed _ = False"

definition vals_compare_safe :: "val \<Rightarrow> val \<Rightarrow> bool" where 
  "vals_compare_safe v1 v2 = (val_is_unboxed v1 \<or> val_is_unboxed v2)"

(** Evaluation contexts *)
datatype ectx_item =
  AppLCtx val
  | AppRCtx expr
  | UnOpCtx un_op
  | BinOpLCtx bin_op val
  | BinOpRCtx bin_op expr
  | IfCtx expr expr
  | PairLCtx val
  | PairRCtx expr
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx expr expr
  | AllocNLCtx val
  | AllocNRCtx expr
  | FreeCtx
  | LoadCtx
  | StoreLCtx val
  | StoreRCtx expr
  | XchgLCtx val
  | XchgRCtx expr
  | CmpXchgLCtx val val
  | CmpXchgMCtx expr val
  | CmpXchgRCtx expr expr
  | FaaLCtx val
  | FaaRCtx expr
  | ResolveLCtx ectx_item val val
  | ResolveMCtx expr val
  | ResolveRCtx expr expr

fun fill_item :: "ectx_item \<Rightarrow> expr \<Rightarrow> expr" where
  "fill_item (AppLCtx v2) e = App e (of_val v2)"
| "fill_item (AppRCtx e1) e = App e1 e"
| "fill_item (UnOpCtx op) e = UnOp op e"
| "fill_item (BinOpLCtx op v2) e = BinOp op e (Val v2)"
| "fill_item (BinOpRCtx op e1) e = BinOp op e1 e"
| "fill_item (IfCtx e1 e2) e = If e e1 e2"
| "fill_item (PairLCtx v2) e = Pair e (Val v2)"
| "fill_item (PairRCtx e1) e = Pair e1 e"
| "fill_item FstCtx e = Fst e"
| "fill_item SndCtx e = Snd e"
| "fill_item InjLCtx e = InjL e"
| "fill_item InjRCtx e = InjR e"
| "fill_item (CaseCtx e1 e2) e = Case e e1 e2"
| "fill_item (AllocNLCtx v2) e = AllocN e (Val v2)"
| "fill_item (AllocNRCtx e1) e = AllocN e1 e"
| "fill_item FreeCtx e = Free e"
| "fill_item LoadCtx e = Load e"
| "fill_item (StoreLCtx v2) e = Store e (Val v2)"
| "fill_item (StoreRCtx e1) e = Store e1 e"
| "fill_item (XchgLCtx v2) e = Xchg e (Val v2)"
| "fill_item (XchgRCtx e1) e = Xchg e1 e"
| "fill_item (CmpXchgLCtx v1 v2) e = CmpXchg e (Val v1) (Val v2)"
| "fill_item (CmpXchgMCtx e0 v2) e = CmpXchg e0 e (Val v2)"
| "fill_item (CmpXchgRCtx e0 e1) e = CmpXchg e0 e1 e"
| "fill_item (FaaLCtx v2) e = FAA e (Val v2)"
| "fill_item (FaaRCtx e1) e = FAA e1 e"
| "fill_item (ResolveLCtx K v1 v2) e = Resolve (fill_item K e) (Val v1) (Val v2)"
| "fill_item (ResolveMCtx ex v2) e = Resolve ex e (Val v2)"
| "fill_item (ResolveRCtx ex e1) e = Resolve ex e1 e"

fun subst :: "string \<Rightarrow> val \<Rightarrow> expr \<Rightarrow> expr" where
  "subst _ _ (Val v) = Val v"
| "subst x v (Var y) = (if x=y then Val v else Var y)"
| "subst x v (Rec f y e) = Rec f y (if (Some x \<noteq> f \<and> Some x \<noteq> y) then subst x v e else e)"
| "subst x v (App e1 e2) = App (subst x v e1) (subst x v e2)"
| "subst x v (UnOp op e) = UnOp op (subst x v e)"
| "subst x v (BinOp op e1 e2) = BinOp op (subst x v e1) (subst x v e2)"
| "subst x v (If e0 e1 e2) = If (subst x v e0) (subst x v e1) (subst x v e2)"
| "subst x v (Pair e1 e2) = Pair (subst x v e1) (subst x v e2)"
| "subst x v (Fst e) = Fst (subst x v e)"
| "subst x v (Snd e) = Snd (subst x v e)"
| "subst x v (InjL e) = InjL (subst x v e)"
| "subst x v (InjR e) = InjR (subst x v e)"
| "subst x v (Case e0 e1 e2) = Case (subst x v e0) (subst x v e1) (subst x v e2)"
| "subst x v (Fork e) = Fork (subst x v e)"
| "subst x v (AllocN e1 e2) = AllocN (subst x v e1) (subst x v e2)"
| "subst x v (Free e) = Free (subst x v e)"
| "subst x v (Load e) = Load (subst x v e)"
| "subst x v (Xchg e1 e2) = Xchg (subst x v e1) (subst x v e2)"
| "subst x v (Store e1 e2) = Store (subst x v e1) (subst x v e2)"
| "subst x v (CmpXchg e0 e1 e2) = CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)"
| "subst x v (FAA e1 e2) = FAA (subst x v e1) (subst x v e2)"
| "subst _ _ NewProph = NewProph"
| "subst x v (Resolve ex e1 e2) = Resolve (subst x v ex) (subst x v e1) (subst x v e2)"

definition subst' :: "binder_t \<Rightarrow> val \<Rightarrow> expr \<Rightarrow> expr" where
  "subst' mx v = (case mx of Some x \<Rightarrow> subst x v | None \<Rightarrow> (\<lambda>x. x))"

(* The stepping relation *)
fun un_op_eval :: "un_op \<Rightarrow> val \<Rightarrow> val option" where
  "un_op_eval NegOp (LitV (LitBool b)) = Some (LitV (LitBool (\<not> b)))"
| "un_op_eval NegOp (LitV (LitInt n)) = Some (LitV (LitInt (not n)))"
| "un_op_eval MinusUnOp (LitV (LitInt n)) = Some (LitV (LitInt (- n)))"
| "un_op_eval _ _ = None"

fun bin_op_eval_int :: "bin_op \<Rightarrow> int \<Rightarrow> int \<Rightarrow> base_lit option" where
  "bin_op_eval_int PlusOp n1 n2 = Some (LitInt (n1 + n2))"
| "bin_op_eval_int MinusOp n1 n2 = Some (LitInt (n1 - n2))"
| "bin_op_eval_int MultOp n1 n2 = Some (LitInt (n1 * n2))"
| "bin_op_eval_int QuotOp n1 n2 = Some (LitInt (n1 div n2))"
| "bin_op_eval_int RemOp n1 n2 = Some (LitInt (n1 mod n2))"
| "bin_op_eval_int AndOp n1 n2 = Some (LitInt (and n1 n2))"
| "bin_op_eval_int OrOp n1 n2 = Some (LitInt (or n1 n2))"
| "bin_op_eval_int XorOp n1 n2 = Some (LitInt (xor n1 n2))"
| "bin_op_eval_int ShiftLOp n1 n2 = Some (LitInt (push_bit (nat n1) n2))"
| "bin_op_eval_int ShiftROp n1 n2 = Some (LitInt (drop_bit (nat n1) n2))"
| "bin_op_eval_int LeOp n1 n2 = Some (LitBool (n1 \<le> n2))"
| "bin_op_eval_int LtOp n1 n2 = Some (LitBool (n1 < n2))"
| "bin_op_eval_int EqOp n1 n2 = Some (LitBool (n1 = n2))"
| "bin_op_eval_int OffsetOp _ _ = None" (* Pointer arithmetic *)

fun bin_op_eval_bool :: "bin_op \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> base_lit option" where
  "bin_op_eval_bool AndOp b1 b2 = Some (LitBool (b1 \<and> b2))"
| "bin_op_eval_bool OrOp b1 b2 = Some (LitBool (b1 \<or> b2))"
| "bin_op_eval_bool XorOp b1 b2 = Some (LitBool ((\<not>b1\<and>b2)\<or>(b1\<and>\<not>b2)))"
| "bin_op_eval_bool EqOp b1 b2 = Some (LitBool (b1 = b2))"
| "bin_op_eval_bool _ _ _ = None"

fun bin_op_eval_loc :: "bin_op \<Rightarrow> loc \<Rightarrow> base_lit \<Rightarrow> base_lit option" where
  "bin_op_eval_loc OffsetOp l (LitInt off) = Some (LitLoc (l+\<^sub>\<iota>off))"
| "bin_op_eval_loc _ _ _ = None"


definition bin_op_eval :: "bin_op \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option" where
  "bin_op_eval op v1 v2 = 
  (if (op = EqOp) then
      if (vals_compare_safe v1 v2) then
        Some (LitV (LitBool (v1 = v2)))
      else
        None
   else (case (v1, v2) of
      (LitV (LitInt n1), LitV (LitInt n2)) \<Rightarrow> map_option LitV (bin_op_eval_int op n1 n2)
      | (LitV (LitBool b1), LitV (LitBool b2)) \<Rightarrow> map_option LitV (bin_op_eval_bool op b1 b2)
      | (LitV (LitLoc l1), LitV v2) \<Rightarrow> map_option LitV (bin_op_eval_loc op l1 v2)
      | (_, _) \<Rightarrow> None)
    )"
end