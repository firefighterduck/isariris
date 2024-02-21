theory State
imports HeapLang
begin

section \<open> State \<close>
text \<open> State specific definitions and lemmata; 
  based on \<^url>\<open>https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lang.v\<close> \<close>

(* The state: heaps of val options, with None representing deallocated locations. *)
datatype state = State (heap: "(loc,val option) fmap") (used_proph_id: "proph_id fset")

definition state_upd_heap :: "((loc,val option) fmap \<Rightarrow> (loc,val option) fmap) \<Rightarrow> state \<Rightarrow> state" where
  "state_upd_heap f \<sigma> = State (f (heap \<sigma>)) (used_proph_id \<sigma>)"

definition state_upd_used_proph_id :: "(proph_id fset \<Rightarrow> proph_id fset) \<Rightarrow> state \<Rightarrow> state" where
  "state_upd_used_proph_id f \<sigma> = State (heap \<sigma>) (f (used_proph_id \<sigma>))"

lemma state_upd_proph: "used_proph_id (state_upd_heap f \<sigma>) = used_proph_id \<sigma>"
  unfolding state_upd_heap_def by simp

fun heap_array :: "loc \<Rightarrow> val list \<Rightarrow> (loc, val option) fmap" where
  "heap_array l [] = fmempty"
| "heap_array l (v#vs) = fmupd l (Some v) (heap_array (l+\<^sub>\<iota>1) vs)"
  
lemma heap_array_singleton: "heap_array l [v] = fmupd l (Some v) fmempty" by simp

lemma heap_array_dom: "fmdom (heap_array l vs) = Abs_fset {l ..< (l +\<^sub>\<iota> int (length vs))}"
proof (induction vs arbitrary: l)
  case Nil
  then show ?case by (auto simp: loc_add_0 bot_fset.abs_eq)
next
  case (Cons a vs)
  have "fmdom (heap_array l (a # vs)) = finsert l (fmdom (heap_array (l+\<^sub>\<iota>1) vs))" by simp
  then have "fset (fmdom (heap_array l (a # vs))) = insert l (fset (fmdom (heap_array (l+\<^sub>\<iota>1) vs)))"
    by simp
  also have "... = insert l (fset (Abs_fset {(l+\<^sub>\<iota>1)..< ((l+\<^sub>\<iota>1) +\<^sub>\<iota> int (length vs))}))" 
    using Cons by simp
  also have "... = insert l {(l+\<^sub>\<iota>1)..< ((l+\<^sub>\<iota>1) +\<^sub>\<iota> int (length vs))}"
    using Abs_fset_inverse finite_atLeastLessThan_loc by blast
  also have "... = {l} \<union> {(l+\<^sub>\<iota>1)..< ((l+\<^sub>\<iota>1) +\<^sub>\<iota> int (length vs))}"
    by simp
  also have "... = {l..<(l+\<^sub>\<iota>1)} \<union> {(l+\<^sub>\<iota>1)..<((l+\<^sub>\<iota>1) +\<^sub>\<iota> int (length vs))}" 
    using less_eq_loc_def loc_add_def less_loc_def loc.expand finite_atLeastLessThan_int by auto
  also have "... = ({l..<(l+\<^sub>\<iota>1)} \<union> {(l+\<^sub>\<iota>1)..<(l+\<^sub>\<iota>(1 + int (length vs)))})" by (simp add: loc_add_assoc)
  also have "... = ({l..<(l+\<^sub>\<iota>1)} \<union> {(l+\<^sub>\<iota>1)..<(l+\<^sub>\<iota> int (length (a#vs)))})" by simp
  also have "... = {l..<(l +\<^sub>\<iota> int (length (a#vs)))}" 
    by (auto simp: loc_add_def loc.expand less_eq_loc_def ivl_disj_un(17))
  finally have "Abs_fset (fset (fmdom (heap_array l (a # vs)))) = Abs_fset {l..<(l +\<^sub>\<iota> int (length (a#vs)))}"
    by simp
  then show ?case unfolding fset_inverse .
qed 

lemma heap_array_shift: "fmlookup (heap_array l vs) k = fmlookup (heap_array (l+\<^sub>\<iota>n) vs) (k+\<^sub>\<iota>n)"
proof (induction vs arbitrary: l k)
  case (Cons a vs)
  show ?case apply (simp; rule impI; rule conjI) using loc_add_def apply (simp_all add: loc.expand) 
    using Cons using loc_add_def loc.expand apply blast
    by (smt (verit) loc.sel local.Cons)
qed (simp)

term fset

lemma heap_array_cons_shift: "(fmlookup (heap_array l vs) k = Some w) \<Longrightarrow> 
  (fmlookup (heap_array l (v#vs)) (k+\<^sub>\<iota>1) = Some w)"
proof -
  assume assm: "fmlookup (heap_array l vs) k = Some w"
  hence "k |\<in>| fmdom (heap_array l vs)" by (rule fmdomI)
  then have "k \<in> {l ..< (l +\<^sub>\<iota> int (length vs))}" unfolding heap_array_dom
    using Abs_fset_inverse by blast
  then have "l\<noteq>k+\<^sub>\<iota>1"  using less_eq_loc_def loc_add_def by force
  with assm show "fmlookup (heap_array l (v#vs)) (k+\<^sub>\<iota>1) = Some w" unfolding loc_add_def apply simp 
  using heap_array_shift loc_add_def by fastforce
qed

lemma heap_array_elements: "fmlookup (heap_array l vs) k = Some (Some w) \<Longrightarrow> w \<in> set vs"
proof (induction vs arbitrary: l k)
  case (Cons a vs)
  then show ?case by (metis fmupd_lookup heap_array.simps(2) in_set_member member_rec(1) option.inject)
qed (simp)

lemma heap_array_step: "\<lbrakk>fmlookup (heap_array l (v#vs)) k = Some w; l\<noteq>k\<rbrakk> \<Longrightarrow> 
  fmlookup (heap_array l vs) (k+\<^sub>\<iota>(-1)) = Some w"
proof (induction vs arbitrary: l k v)
  case (Cons a vs)
  from Cons(3) have "fmlookup (heap_array l (v # a # vs)) k = fmlookup (heap_array (l+\<^sub>\<iota>1) (a#vs)) k" 
    by simp
  with Cons(2) have step: "fmlookup (heap_array (l+\<^sub>\<iota>1) (a#vs)) k = Some w" by simp
  then show ?case proof (cases "(l+\<^sub>\<iota>1=k)")
    case True
    with step have "w=Some a" by simp
    with True show ?thesis unfolding loc_add_def by auto
  next
    case False
    from Cons(3) have "fmlookup (heap_array l (a # vs)) (k +\<^sub>\<iota> - 1) = fmlookup (heap_array (l+\<^sub>\<iota>1) vs) (k +\<^sub>\<iota> - 1)"
      using loc_add_def False by force
    with Cons(1)[OF step False] show ?thesis by simp
  qed
qed (simp)

(* Due to nth being defined as primrec, this can't be an iff but only a one sided implication. *)
lemma heap_array_lookup: "(fmlookup (heap_array l vs) k = Some (Some ow)) \<Longrightarrow>
  (\<exists>j w. 0 \<le> j \<and> k = l +\<^sub>\<iota> j \<and> vs!(nat j) = w \<and> w=ow)"
proof (induction vs arbitrary: k)
  case (Cons a vs)
  then show ?case proof (cases "l=k")
    case True
    hence "fmlookup (heap_array l (a#vs)) k = Some (Some a)" by simp
    with Cons(2) have "ow = a" by simp
    moreover from True have "k=l+\<^sub>\<iota>0 \<and> (0::int)\<le>0 \<and> (a#vs)!(nat 0) = a" by (simp add: loc_add_0)
    ultimately show ?thesis by blast
  next
    case False
    from Cons(1)[OF heap_array_step[OF Cons(2) False]] obtain j w 
      where jw: "0 \<le> j \<and> k +\<^sub>\<iota> - 1 = l +\<^sub>\<iota> j \<and> vs ! nat j = w \<and> w = ow" by blast
    hence "0\<le>j+1 \<and> k=l+\<^sub>\<iota>(j+1) \<and> (a#vs)!(nat (j+1)) = w \<and> w = ow" by (simp add: loc_add_def)
      (smt (verit, ccfv_SIG) loc.collapse nat_1 nat_diff_distrib)
    then show ?thesis by fast
  qed
qed (simp)

lemma state_array_map_disjoint: "(\<forall>i. (0\<le>i \<longrightarrow> (nat i < length vs) \<longrightarrow> fmlookup h (l+\<^sub>\<iota>i) = None))
  \<Longrightarrow> fmdom (heap_array l vs) |\<inter>| fmdom h = {||}"
proof
  assume assm: "\<forall>i\<ge>0. nat i < length vs \<longrightarrow> fmlookup h (l +\<^sub>\<iota> i) = None"
  from assm have "\<forall>i\<ge>0. nat i < length vs \<longrightarrow> (l +\<^sub>\<iota> i) |\<notin>| fmdom h" by fastforce
  hence "\<forall>i \<in> {0..<(int (length vs))}. (l +\<^sub>\<iota> i) |\<notin>| fmdom h" by fastforce
  hence "\<forall>l' \<in> {(l +\<^sub>\<iota> i) | i. i \<in> {0..<(int (length vs))} }. l' |\<notin>| fmdom h" by blast
  hence "\<forall>l' \<in> {l..<(l +\<^sub>\<iota> int (length vs))}. l' |\<notin>| fmdom h" using loc_ranges by blast
  hence "Abs_fset {l..<(l +\<^sub>\<iota> int (length vs))} |\<inter>| fmdom h = {||}"
    using Abs_fset_inverse by blast
  with heap_array_dom show "fmdom (heap_array l vs) |\<inter>| fmdom h |\<subseteq>| {||}" by auto
qed (simp)

definition state_init_heap :: "loc \<Rightarrow> nat \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "state_init_heap l n v \<sigma> = state_upd_heap (\<lambda>h. h ++\<^sub>f heap_array l (replicate n v)) \<sigma>"

lemma state_init_heap_singleton: "state_init_heap l 1 v \<sigma> = state_upd_heap (\<lambda>h. fmupd l (Some v) h) \<sigma>"
unfolding state_init_heap_def by simp

inductive head_step :: "expr \<Rightarrow> state \<Rightarrow> observation list \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> bool" 
  ("_ _ _ \<Rightarrow>\<^sub>h _ _ _")  where
  RecS: "(Rec f x e) \<sigma> [] \<Rightarrow>\<^sub>h (Val(RecV f x e)) \<sigma> []"
| PairS: "(Pair (Val v1) (Val v2)) \<sigma> [] \<Rightarrow>\<^sub>h (Val(PairV v1 v2)) \<sigma> []"
| InjLS: "(InjL(Val v)) \<sigma> [] \<Rightarrow>\<^sub>h (Val(InjLV v)) \<sigma> []"
| InjRS: "(InjR(Val v)) \<sigma> [] \<Rightarrow>\<^sub>h (Val(InjRV v)) \<sigma> []"
| BetaS: "e' = subst' x v2 (subst' f (RecV f x e1) e1) \<Longrightarrow>
  (App (Val(RecV f x e1)) (Val v2)) \<sigma> [] \<Rightarrow>\<^sub>h e' \<sigma> []"
| UnOpS: "un_op_eval op v = Some v' \<Longrightarrow>
  (UnOp op (Val v)) \<sigma> [] \<Rightarrow>\<^sub>h (Val v') \<sigma> []"
| BinOpS: "bin_op_eval op v1 v2 = Some v' \<Longrightarrow>
  (BinOp op (Val v1) (Val v2)) \<sigma> [] \<Rightarrow>\<^sub>h (Val v') \<sigma> []"
| IfTrueS: "(If (Val(LitV(LitBool True))) e1 e2) \<sigma> [] \<Rightarrow>\<^sub>h e1 \<sigma> []"
| IfFalseS: "(If (Val(LitV(LitBool False))) e1 e2) \<sigma> [] \<Rightarrow>\<^sub>h e2 \<sigma> []"
| FstS: "(Fst (Val(PairV v1 v2))) \<sigma> [] \<Rightarrow>\<^sub>h (Val v1) \<sigma> []"
| SndS: "(Snd (Val(PairV v1 v2))) \<sigma> [] \<Rightarrow>\<^sub>h (Val v2) \<sigma> []"
| CaseLS: "(Case (Val(InjLV v)) e1 e2) \<sigma> [] \<Rightarrow>\<^sub>h (App e1 (Val v)) \<sigma> []"
| CaseRS: "(Case (Val(InjRV v)) e1 e2) \<sigma> [] \<Rightarrow>\<^sub>h (App e2 (Val v)) \<sigma> []"
| ForkS: "(Fork e) \<sigma> [] \<Rightarrow>\<^sub>h (Val(LitV LitUnit)) \<sigma> [e]"
| AllocNS: "\<lbrakk>(0 < n); (\<forall> (i::int). (0 \<le> i) \<longrightarrow> (i < n) \<longrightarrow> fmlookup (heap \<sigma>) (l +\<^sub>\<iota> i) = None)\<rbrakk> \<Longrightarrow>
  (AllocN (Val(LitV(LitInt n))) (Val v)) \<sigma> [] \<Rightarrow>\<^sub>h
  (Val(LitV(LitLoc l))) (state_init_heap l (nat n) v \<sigma>) []"
| FreeS: "fmlookup (heap \<sigma>) l = Some v \<Longrightarrow> 
  (Free (Val(LitV(LitLoc l)))) \<sigma> [] \<Rightarrow>\<^sub>h (Val(LitV LitUnit)) (state_upd_heap (\<lambda>h. fmupd l None h) \<sigma>) []"
| LoadS: "fmlookup (heap \<sigma>) l = Some (Some v) \<Longrightarrow> (Load (Val(LitV(LitLoc l)))) \<sigma> [] \<Rightarrow>\<^sub>h (of_val v) \<sigma> []"
| StoreS: "fmlookup (heap \<sigma>) l = Some (Some v) \<Longrightarrow>
  (Store (Val(LitV(LitLoc l))) (Val w)) \<sigma> [] \<Rightarrow>\<^sub>h
  (Val(LitV LitUnit)) (state_upd_heap (\<lambda>h. fmupd l (Some w) h) \<sigma>) []"
| XchgS: "fmlookup (heap \<sigma>) l = Some (Some v1) \<Longrightarrow>
  (Xchg (Val(LitV(LitLoc l))) (Val v2)) \<sigma> [] \<Rightarrow>\<^sub>h
  (Val v1) (state_upd_heap (\<lambda>h. fmupd l (Some v2) h) \<sigma>) []"
   (* Crucially, this compares the same way as [EqOp]! *)
| CmpXchgS: "\<lbrakk>fmlookup (heap \<sigma>) l = Some (Some vl); vals_compare_safe vl v1; b = (vl = v1)\<rbrakk> \<Longrightarrow>
  (CmpXchg (Val(LitV(LitLoc l))) (Val v1) (Val v2)) \<sigma> [] \<Rightarrow>\<^sub>h
  (Val(PairV vl (LitV(LitBool b)))) (if b then state_upd_heap (\<lambda>h. fmupd l (Some v2) h) \<sigma> else \<sigma>) []"
| FaaS: "fmlookup (heap \<sigma>) l = Some (Some (LitV (LitInt i1))) \<Longrightarrow>
  (FAA (Val(LitV(LitLoc l))) (Val(LitV(LitInt i2)))) \<sigma> [] \<Rightarrow>\<^sub>h
  (Val(LitV(LitInt i1))) (state_upd_heap (\<lambda>h. fmupd l (Some (LitV (LitInt (i1 + i2)))) h) \<sigma>) []"
| NewProphS: "p |\<notin>| used_proph_id \<sigma> \<Longrightarrow>
  NewProph \<sigma> [] \<Rightarrow>\<^sub>h (Val(LitV(LitProphecy p))) (state_upd_used_proph_id (finsert p) \<sigma>) []"
| ResolveS: "e \<sigma> \<kappa>s \<Rightarrow>\<^sub>h (Val v) \<sigma>' ts \<Longrightarrow>
  (Resolve e (Val(LitV(LitProphecy p))) (Val w)) \<sigma> (\<kappa>s@[(p, (v, w))]) \<Rightarrow>\<^sub>h (Val v) \<sigma>' ts"
 
declare head_step.intros[intro]
inductive_cases headE[elim]: "(Rec f x e) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(Pair v1 v2) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(InjL v) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(InjR v) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(App f v2) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e' \<sigma>2 \<kappa>2"
  "(UnOp op v) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(BinOp op v1 v2) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(If b e1 e2) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e' \<sigma>2 \<kappa>2"
  "(Fst v) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(Snd v) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(Case v e1 e2) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2' \<sigma>2 \<kappa>2"
  "(Fork e) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs"
  "(AllocN e v) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(Free l) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(Load l) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(Store l v) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(Xchg l v) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(CmpXchg l v1 v2) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(FAA l i) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "NewProph \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  "(Resolve e v1 w) \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 \<kappa>2"
  
lemma fill_item_val: "\<exists>x. Some x = (to_val (fill_item Ki e)) \<Longrightarrow> \<exists>x. Some x = (to_val e)"
by (induct Ki) auto

lemma val_head_stuck: "(e1 \<sigma>1 \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs) \<Longrightarrow> (to_val e1 = None)"
by (induct rule: head_step.induct) auto

lemma head_ctx_step_val: "(fill_item Ki e) \<sigma>1 \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs \<Longrightarrow> \<exists>x. Some x = (to_val e)"
proof (induction Ki arbitrary: \<kappa> e2)
  case (CaseCtx x1a x2a)
  then show ?case by cases auto
next
  case (ResolveLCtx Ki v1 v2)
  hence step: "(Resolve (fill_item Ki e) (Val v1) (Val v2)) \<sigma>1 \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs" by simp
  show ?case by (rule headE(21)[OF step, of "\<exists>x. Some x = to_val e"]) (simp add: ResolveLCtx(1))
next
  case (ResolveMCtx x1a x2a)
  then show ?case by cases auto
next
  case (ResolveRCtx x1a x2a)
  then show ?case by cases auto
qed auto

lemma fill_item_no_val_inj: "\<lbrakk>to_val e1 = None; to_val e2 = None; fill_item Ki1 e1 = fill_item Ki2 e2\<rbrakk>
   \<Longrightarrow> Ki1 = Ki2"
proof (induction Ki2 arbitrary: Ki1)
  case (AppLCtx x)
  then show ?case by (cases Ki1) auto
next
  case (AppRCtx x)
  then show ?case by (cases Ki1) auto
next
  case (UnOpCtx x)
  then show ?case by (cases Ki1) auto
next
  case (BinOpLCtx x1a x2a)
  then show ?case by (cases Ki1) auto
next
  case (BinOpRCtx x1a x2a)
  then show ?case by (cases Ki1) auto
next
  case (IfCtx x1a x2a)
  then show ?case by (cases Ki1) auto
next
  case (PairLCtx x)
  then show ?case by (cases Ki1) auto
next
  case (PairRCtx x)
  then show ?case by (cases Ki1) auto
next
  case FstCtx
  then show ?case by (cases Ki1) auto
next
  case SndCtx
  then show ?case by (cases Ki1) auto
next
  case InjLCtx
  then show ?case by (cases Ki1) auto
next
  case InjRCtx
  then show ?case by (cases Ki1) auto
next
  case (CaseCtx x1a x2a)
  then show ?case by (cases Ki1) auto
next
  case (AllocNLCtx x)
  then show ?case by (cases Ki1) auto
next
  case (AllocNRCtx x)
  then show ?case by (cases Ki1) auto
next
  case FreeCtx
  then show ?case by (cases Ki1) auto
next
  case LoadCtx
  then show ?case by (cases Ki1) auto
next
  case (StoreLCtx x)
  then show ?case by (cases Ki1) auto
next
  case (StoreRCtx x)
  then show ?case by (cases Ki1) auto
next
  case (XchgLCtx x)
  then show ?case by (cases Ki1) auto
next
  case (XchgRCtx x)
  then show ?case by (cases Ki1) auto
next
  case (CmpXchgLCtx x1a x2a)
  then show ?case by (cases Ki1) auto
next
  case (CmpXchgMCtx x1a x2a)
  then show ?case by (cases Ki1) auto
next
  case (CmpXchgRCtx x1a x2a)
  then show ?case by (cases Ki1) auto
next
  case (FaaLCtx x)
  then show ?case by (cases Ki1) auto
next
  case (FaaRCtx x)
  then show ?case by (cases Ki1) auto
next
  case (ResolveLCtx Ki2 x2a x3a)
  then show ?case by (cases Ki1) auto
next
  case (ResolveMCtx x1a x2a)
  then show ?case by (cases Ki1) auto
next
  case (ResolveRCtx x1a x2a)
  then show ?case by (cases Ki1) auto
qed

lemma alloc_fresh:  "(0 < n) \<Longrightarrow>
  (AllocN ((Val(LitV(LitInt n)))) (Val v)) \<sigma> [] \<Rightarrow>\<^sub>h
  (Val(LitV(LitLoc (fresh_locs (sorted_list_of_fset (fmdom (heap \<sigma>))))))) 
    (state_init_heap (fresh_locs (sorted_list_of_fset (fmdom (heap \<sigma>)))) (nat n) v \<sigma>) []"
  apply (rule AllocNS) using fresh_locs_fresh[of _ "(sorted_list_of_fset (fmdom (heap \<sigma>)))"] 
  by (auto simp : fmdom'_alt_def fmdom'_notD)
  
lemma head_step_to_val: "\<lbrakk>e1 \<sigma>1 \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs; e1 \<sigma>1' \<kappa>' \<Rightarrow>\<^sub>h e2' \<sigma>2' efs'; \<exists>x. Some x = (to_val e2)\<rbrakk>
  \<Longrightarrow> \<exists>x. Some x = (to_val e2')"
  by (induction rule: head_step.induct) auto

lemma fill_item_not_val: "False \<longleftrightarrow> (of_val v = fill_item K e)"
  by (induction K) auto
  
(* Other lemmata contain references to the Iris base logic and can thus not be defined yet. *)
end
