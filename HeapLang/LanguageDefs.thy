theory LanguageDefs
imports PrimitiveLaws State "../IrisCore/AuthHeap" "../IrisCore/Invariant" "../IrisCore/iPropShallow"
begin

text \<open>Heap camera setup\<close>
interpretation heapInG: inG get_heap upd_heap
apply (auto simp: inG_def get_heap_def upd_heap_def prod_n_valid_def \<epsilon>_n_valid op_prod_def \<epsilon>_left_id)
apply (prefer_last,metis surj_pair single_map_ne d_equiv)
apply (auto simp: pcore_prod_def pcore_fun_def \<epsilon>_fun_def \<epsilon>_option_def pcore_option_def comp_def 
  split: option.splits)
apply (auto simp: op_fun_def op_option_def)
apply (auto simp: valid_raw_fun.rep_eq valid_raw_option_def incl_def n_equiv_fun_def 
  n_equiv_option_def split: option.splits)
apply metis
apply metis
apply presburger
apply (auto simp: upd_heap_def get_heap_def)
done

abbreviation "points_to_heap \<equiv> points_to upd_heap"
abbreviation "points_to_disc_heap \<equiv> points_to_disc upd_heap"
abbreviation "points_to_own_heap \<equiv> points_to_own upd_heap"
abbreviation "points_to_full_heap \<equiv> points_to_full upd_heap"

bundle heap_syntax begin
notation points_to_heap ("_ \<mapsto>{_} _" 60)
notation points_to_disc_heap (infix "\<mapsto>\<box>" 60)
notation points_to_own_heap ("_\<mapsto>{#_}_" 60)
notation points_to_full_heap (infix "\<mapsto>\<^sub>u" 60)
end

declare timeless_points_to[OF heapInG.inG_axioms, timeless_rule,log_prog_rule]

text \<open>Auxiliary language specific definitions\<close>

context
fixes  get_prophm :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> heap_lang_proph_map option"
  and put_prophm
  and get_heap :: "gname \<Rightarrow> 'res \<Rightarrow> heap_lang_heap option"
  and put_heap
assumes proph_inG: "inG get_prophm put_prophm"
  and heap_inG: "inG get_heap put_heap"
begin
definition state_interp :: "state \<Rightarrow> observation list \<Rightarrow> 'res upred_f" where
  "state_interp \<sigma> \<kappa>s = heap_interp put_heap (heap \<sigma>) \<^emph> proph_map_interp put_prophm \<kappa>s (used_proph_id \<sigma>)"
end
  
definition fill :: "ectx_item list \<Rightarrow> expr \<Rightarrow> expr"  where "fill K e = foldl (\<lambda>exp ctx. fill_item ctx exp) e K"

lemma fill_item_Rec: "fill_item K' e2 \<noteq> Rec f x e" by (induction K') auto
lemma fill_Rec: "fill K e' = Rec f x e \<Longrightarrow> K =[] \<and> e' = Rec f x e"
  apply (induction K arbitrary: e') apply (auto simp: fill_def) using fill_item_Rec by blast

lemma fill_store: "fill K e = Store (Val v1) (Val v2) \<Longrightarrow> 
  (K = [] \<and> e = Store (Val v1) (Val v2)) \<or> (\<exists>K'. K = K'@[StoreLCtx v2] \<or> K = K'@[StoreRCtx (Val v1)])"
proof (induction K arbitrary: e)
  case Nil
  have "fill [] e = e" unfolding fill_def by simp
  with Nil show ?case by simp
next
  case (Cons a K)
  then have "fill K (fill_item a e) = Store (of_val v1) (of_val v2)" unfolding fill_def by simp
  then have "K = [] \<and> (fill_item a e) = Store (of_val v1) (of_val v2) \<or> (\<exists>K'. K = K' @ [StoreLCtx v2] \<or> K = K' @ [StoreRCtx (of_val v1)])"
    using Cons(1) by auto
  then have "(K = [] \<and> (a = StoreLCtx v2 \<or> a= StoreRCtx (of_val v1))) 
    \<or> (\<exists>K'. K = K' @ [StoreLCtx v2] \<or> K = K' @ [StoreRCtx (of_val v1)])"
    by (induction a) auto
  then show ?case by auto
qed

lemma fill_faa: "fill K e = FAA (Val v1) (Val v2) \<Longrightarrow> 
  (K = [] \<and> e = FAA (Val v1) (Val v2)) \<or> (\<exists>K'. K = K'@[FaaLCtx v2] \<or> K = K'@[FaaRCtx (Val v1)])"
proof (induction K arbitrary: e)
  case Nil
  have "fill [] e = e" unfolding fill_def by simp
  with Nil show ?case by simp
next
  case (Cons a K)
  then have "fill K (fill_item a e) = FAA (of_val v1) (of_val v2)" unfolding fill_def by simp
  then have "K = [] \<and> (fill_item a e) = FAA (of_val v1) (of_val v2) \<or> (\<exists>K'. K = K' @ [FaaLCtx v2] \<or> K = K' @ [FaaRCtx (of_val v1)])"
    using Cons(1) by auto
  then have "(K = [] \<and> (a = FaaLCtx v2 \<or> a= FaaRCtx (of_val v1))) 
    \<or> (\<exists>K'. K = K' @ [FaaLCtx v2] \<or> K = K' @ [FaaRCtx (of_val v1)])"
    by (induction a) auto
  then show ?case by auto
qed

lemma fill_item_Val: "fill_item K e \<noteq> Val v" by (induction K) auto
lemma fill_Val: "fill K e = Val v \<Longrightarrow> K = [] \<and> e = Val v"
  apply (induction K arbitrary: e) apply (auto simp: fill_def) using fill_item_Val by blast

lemma fill_store_val: "\<lbrakk>Store (of_val v1) (of_val v2) = fill K e; e \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs\<rbrakk> \<Longrightarrow>
  K = [] \<and> e = Store (of_val v1) (of_val v2)"
proof -
  assume assms: "Store (of_val v1) (of_val v2) = fill K e" "e \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs"
  have "K = K' @ [StoreLCtx v2] \<Longrightarrow> fill K e = fill_item (StoreLCtx v2) (fill K' e)" for K'
    unfolding fill_def by simp
  with assms(1) have "K = K' @ [StoreLCtx v2] \<Longrightarrow> fill K' e = Val v1" for K' by simp
  then have "K = K' @ [StoreLCtx v2] \<Longrightarrow> fill K' e = Val v1" for K' by simp
  then have v1: "K = K' @ [StoreLCtx v2] \<Longrightarrow> e = v1" for K' using fill_Val by blast
  have "K = K' @ [StoreRCtx (Val v1)] \<Longrightarrow> fill K e = fill_item (StoreRCtx (Val v1)) (fill K' e)" for K'
    unfolding fill_def by simp
  with assms(1) have "K = K' @ [StoreRCtx (Val v1)] \<Longrightarrow> fill K' e = Val v2" for K' by simp
  then have v2: "K = K' @ [StoreRCtx (Val v1)] \<Longrightarrow> e = Val v2" for K' using fill_Val by blast
  with fill_store[OF assms(1)[symmetric]] v1 have "e = Store (of_val v1) (of_val v2) \<or> e = Val v1 \<or> e = Val v2" by blast
  with assms(2) have e: "e = Store (of_val v1) (of_val v2)"
    by (metis option.simps(3) to_val.simps(1) val_head_stuck)
  with v1 v2 fill_store[OF assms(1)[symmetric]] have K: "K = []" by auto
  with e show ?thesis by simp
qed

lemma fill_faa_val: "\<lbrakk>FAA (of_val v1) (of_val v2) = fill K e; e \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs\<rbrakk> \<Longrightarrow>
  K = [] \<and> e = FAA (of_val v1) (of_val v2)"
proof -
  assume assms: "FAA (of_val v1) (of_val v2) = fill K e" "e \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2 \<sigma>2 efs"
  have "K = K' @ [FaaLCtx v2] \<Longrightarrow> fill K e = fill_item (FaaLCtx v2) (fill K' e)" for K'
    unfolding fill_def by simp
  with assms(1) have "K = K' @ [FaaLCtx v2] \<Longrightarrow> fill K' e = Val v1" for K' by simp
  then have "K = K' @ [FaaLCtx v2] \<Longrightarrow> fill K' e = Val v1" for K' by simp
  then have v1: "K = K' @ [FaaLCtx v2] \<Longrightarrow> e = v1" for K' using fill_Val by blast
  have "K = K' @ [FaaRCtx (Val v1)] \<Longrightarrow> fill K e = fill_item (FaaRCtx (Val v1)) (fill K' e)" for K'
    unfolding fill_def by simp
  with assms(1) have "K = K' @ [FaaRCtx (Val v1)] \<Longrightarrow> fill K' e = Val v2" for K' by simp
  then have v2: "K = K' @ [FaaRCtx (Val v1)] \<Longrightarrow> e = Val v2" for K' using fill_Val by blast
  with fill_faa[OF assms(1)[symmetric]] v1 have "e = FAA (of_val v1) (of_val v2) \<or> e = Val v1 \<or> e = Val v2" by blast
  with assms(2) have e: "e = FAA (of_val v1) (of_val v2)"
    by (metis option.simps(3) to_val.simps(1) val_head_stuck)
  with v1 v2 fill_faa[OF assms(1)[symmetric]] have K: "K = []" by auto
  with e show ?thesis by simp
qed

lemma fork_no_fill: "Fork x \<noteq> fill_item E e"
  by (cases E) auto

lemma fill_fork: "\<lbrakk>Fork x = fill K e\<rbrakk> \<Longrightarrow> K = [] \<and> e = Fork x"
  using fork_no_fill 
  apply (cases K)
  apply (auto simp: fill_def)
  by (metis (no_types, lifting) append_butlast_last_id foldl_Cons foldl_Nil foldl_append last_ConsR)

datatype langCtxt = FI ectx_item | F "ectx_item list"
fun lang_ctxt :: "langCtxt \<Rightarrow> expr \<Rightarrow> expr" where
  "lang_ctxt (FI K) e = fill_item K e"
| "lang_ctxt (F K) e = fill K e"
  
definition prim_step :: "expr \<Rightarrow> state \<Rightarrow> observation list \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> bool" where
  "prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs \<equiv> \<exists>K e1' e2'. ((e1=fill K e1') \<and> (e2=fill K e2') \<and> head_step e1' \<sigma>1 \<kappa> e2' \<sigma>2 efs)"

lemma prim_step_simp: "head_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs \<Longrightarrow> prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs"
  unfolding prim_step_def fill_def by (metis foldl_Nil)

definition reducible :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "reducible e \<sigma> \<equiv> \<exists>\<kappa> e' \<sigma>' efs. prim_step e \<sigma> \<kappa> e' \<sigma>' efs"

definition head_red :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "head_red e \<sigma> \<equiv> \<exists>\<kappa> e' \<sigma>' efs. head_step e \<sigma> \<kappa> e' \<sigma>' efs"

definition reducible_no_obs :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "reducible_no_obs e \<sigma> \<equiv> \<exists>e' \<sigma>' efs. prim_step e \<sigma> [] e' \<sigma>' efs"

definition head_red_no_obs :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "head_red_no_obs e \<sigma> \<equiv> \<exists>e' \<sigma>' efs. head_step e \<sigma> [] e' \<sigma>' efs"
  
definition irreducible :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "irreducible e \<sigma> \<equiv> \<forall>\<kappa> e' \<sigma>' efs. \<not>prim_step e \<sigma> \<kappa> e' \<sigma>' efs"

definition head_irred :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "head_irred e \<sigma> \<equiv> \<forall>\<kappa> e' \<sigma>' efs. \<not>head_step e \<sigma> \<kappa> e' \<sigma>' efs"
  
definition stuck :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "stuck e \<sigma> \<equiv> (to_val e = None) \<and> irreducible e \<sigma>"

definition head_stuck :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "head_stuck e \<sigma> \<equiv> (to_val e = None) \<and> head_irred e \<sigma>"
  
definition not_stuck :: "expr \<Rightarrow> state \<Rightarrow> bool" where
  "not_stuck e \<sigma> \<equiv> (\<exists>v. to_val e = Some v) \<or> reducible e \<sigma>"

lemma head_red_no_obs_red: "head_red_no_obs e \<sigma> \<Longrightarrow> head_red e \<sigma>" 
  by (auto simp: head_red_no_obs_def head_red_def)
  
lemma head_red_prim_step: "\<lbrakk>head_red e \<sigma>; prim_step e \<sigma> \<kappa> e' \<sigma>' efs\<rbrakk> \<Longrightarrow> head_step e \<sigma> \<kappa> e' \<sigma>' efs"
sorry (* A rather strange proof in Coq that I don't want to replay right now. *)

lemma irred_val: "irreducible (Val v) \<sigma>"
  unfolding irreducible_def prim_step_def
  by (auto simp: fill_Val) (metis fill_Val option.distinct(1) to_val.simps(1) val_head_stuck)

lemma store_red: "fmlookup (heap \<sigma>) l = Some (Some v') \<Longrightarrow> 
  reducible (Store (of_val (LitV (LitLoc l))) (of_val v)) \<sigma>"
  (is "_ \<Longrightarrow> reducible ?e _")
proof (unfold reducible_def prim_step_def)
  assume assm: "fmlookup (heap \<sigma>) l = Some (Some v')"
  have "?e = fill [] ?e" unfolding fill_def by auto
  with StoreS[OF assm] have 
    "?e = fill [] ?e \<and> of_val (LitV LitUnit) = fill [] (of_val (LitV LitUnit))
    \<and> ?e \<sigma> [] \<Rightarrow>\<^sub>h (of_val (LitV LitUnit)) (state_upd_heap (fmupd l (Some v)) \<sigma>) []"
    by (auto simp: fill_def)
  then show "\<exists>\<kappa> e' \<sigma>' efs K e1' e2'. Store (of_val (LitV (LitLoc l))) (of_val v) = fill K e1' \<and> e' = fill K e2' \<and> e1' \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2' \<sigma>' efs"
    by blast  
qed

lemma faa_red: "fmlookup (heap \<sigma>) l = Some (Some (LitV (LitInt i1))) \<Longrightarrow> 
  reducible (FAA (of_val (LitV (LitLoc l))) (of_val (LitV (LitInt i2)))) \<sigma>"
  (is "_ \<Longrightarrow> reducible ?e _")
proof (unfold reducible_def prim_step_def)
  assume assm: "fmlookup (heap \<sigma>) l = Some (Some (LitV (LitInt i1)))"
  have "?e = fill [] ?e" unfolding fill_def by auto
  with FaaS[OF assm] have 
    "?e = fill [] ?e \<and> of_val (LitV (LitInt i1)) = fill [] (of_val (LitV (LitInt i1)))
    \<and> ?e \<sigma> [] \<Rightarrow>\<^sub>h (of_val (LitV (LitInt i1))) (state_upd_heap (fmupd l (Some (LitV (LitInt (i1 + i2))))) \<sigma>) []"
    by (auto simp: fill_def) 
  then show "\<exists>\<kappa> e' \<sigma>' efs K e1' e2'. FAA (of_val (LitV (LitLoc l))) (of_val (LitV (LitInt i2))) = fill K e1' \<and> e' = fill K e2' \<and> e1' \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2' \<sigma>' efs"
    by blast  
qed

lemma fork_red: "reducible (Fork e) \<sigma>" (is "reducible ?e _")
proof (unfold reducible_def prim_step_def)
  have "?e = fill [] ?e" unfolding fill_def by auto
  with ForkS have 
    "?e = fill [] ?e \<and> of_val (LitV LitUnit) = fill [] (of_val (LitV LitUnit))
    \<and> ?e \<sigma> [] \<Rightarrow>\<^sub>h (of_val (LitV LitUnit)) \<sigma> [e]"
    by (auto simp: fill_def) 
  then show "\<exists>\<kappa> e' \<sigma>' efs K e1' e2'. Fork e = fill K e1' \<and> e' = fill K e2' \<and> e1' \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2' \<sigma>' efs"
    by blast  
qed

lemma prim_step_store: "prim_step (Store (of_val (LitV (LitLoc l))) (of_val v)) \<sigma>1 \<kappa> e2 \<sigma>2 efs \<longleftrightarrow>
  ((\<exists>v'. fmlookup (heap \<sigma>1) l = Some (Some v')) \<and> \<kappa>=[] \<and> e2 = Val(LitV LitUnit)
    \<and> \<sigma>2 = (state_upd_heap (\<lambda>h. fmupd l (Some v) h) \<sigma>1) \<and> efs = [])"
  unfolding prim_step_def using fill_store_val
  apply (auto simp: fill_def)
  apply fastforce
  apply (metis foldl_Nil headE(16))
  apply fastforce
  apply fastforce
  apply (metis headE(16))
  using StoreS fill_def prim_step_def prim_step_simp by auto

lemma prim_step_faa: "prim_step (FAA (of_val (LitV (LitLoc l))) (of_val (LitV (LitInt i2)))) \<sigma>1 \<kappa> e2 \<sigma>2 efs \<longleftrightarrow>
  (\<exists>i1. fmlookup (heap \<sigma>1) l = Some (Some (LitV (LitInt i1))) \<and> \<kappa>=[] \<and> e2 = Val(LitV (LitInt i1))
    \<and> \<sigma>2 = (state_upd_heap (\<lambda>h. fmupd l (Some (LitV (LitInt (i1 + i2)))) h) \<sigma>1) \<and> efs = [])"
  unfolding prim_step_def using fill_faa_val fill_Val
  apply (auto simp: fill_def)
  apply fastforce
  by (metis FaaS foldl_Nil)

lemma prim_step_fork: "prim_step (Fork e) \<sigma>1 \<kappa> e2 \<sigma>2 efs \<longleftrightarrow>
  (\<kappa>=[] \<and> e2 = Val(LitV LitUnit) \<and> \<sigma>2 = \<sigma>1 \<and> efs = [e])"
  unfolding prim_step_def using fill_Val fill_fork
  apply (auto simp:)
  apply fast
  apply (metis fill_def foldl_Nil headE(12))
  apply fast
  apply fast
  using ForkS prim_step_def prim_step_simp by presburger
  
datatype stuckness = NotStuck | MaybeStuck
instantiation stuckness :: order begin
fun less_eq_stuckness :: "stuckness \<Rightarrow> stuckness \<Rightarrow> bool" where
  "less_eq_stuckness MaybeStuck NotStuck = False"
| "less_eq_stuckness _ _ = True"
fun less_stuckness :: "stuckness \<Rightarrow> stuckness \<Rightarrow> bool" where
  "less_stuckness MaybeStuck NotStuck = False"
| "less_stuckness MaybeStuck MaybeStuck = False"
| "less_stuckness NotStuck NotStuck = False"
| "less_stuckness _ _ = True"
instance proof
  fix x y :: stuckness
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (cases x; cases y) auto
next
  fix x :: stuckness
  show "x\<le>x" by (cases x) auto
next
  fix x y z :: stuckness
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) auto
next
  fix x y :: stuckness
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) auto
qed
end

datatype atomicity = StronglyAtomic | WeaklyAtomic

definition stuckness_to_atomicity :: "stuckness \<Rightarrow> atomicity" where
  "stuckness_to_atomicity s = (case s of MaybeStuck \<Rightarrow> StronglyAtomic | NotStuck \<Rightarrow> WeaklyAtomic)"

definition atomic :: "atomicity \<Rightarrow> expr \<Rightarrow> bool" where
  "atomic a e \<equiv> \<forall>\<sigma> e' \<kappa> \<sigma>' efs. prim_step e \<sigma> \<kappa> e' \<sigma>' efs \<longrightarrow> 
    (case a of WeaklyAtomic \<Rightarrow> irreducible e' \<sigma>' | StronglyAtomic \<Rightarrow> (\<exists>v. to_val e' = Some v))"

lemma atomicE: "atomic a e \<Longrightarrow> (\<And>\<sigma> e' \<kappa> \<sigma>' efs. prim_step e \<sigma> \<kappa> e' \<sigma>' efs \<Longrightarrow>
  (case a of WeaklyAtomic \<Rightarrow> irreducible e' \<sigma>' | StronglyAtomic \<Rightarrow> (\<exists>v. to_val e' = Some v)))"
  unfolding atomic_def by meson
  
named_theorems atomic_rule
method atomic_solver = (rule atomic_rule)+    
    
definition head_atomic :: "atomicity \<Rightarrow> expr \<Rightarrow> bool" where
  "head_atomic a e \<equiv> \<forall>\<sigma> e' \<kappa> \<sigma>' efs. head_step e \<sigma> \<kappa> e' \<sigma>' efs \<longrightarrow> 
    (case a of WeaklyAtomic \<Rightarrow> irreducible e' \<sigma>' | StronglyAtomic \<Rightarrow> (\<exists>v. to_val e' = Some v))"
    
type_synonym lan_cfg = "expr list \<times> state"
    
definition step :: "lan_cfg \<Rightarrow> observation list \<Rightarrow> lan_cfg \<Rightarrow> bool" where
  "step p1 \<kappa> p2 \<equiv> \<exists>t1 e1 t2 \<sigma>1 e2 efs \<sigma>2. p1 = (t1@e1#t2, \<sigma>1) \<and> p2 = (t1@e2#t2@efs, \<sigma>2) \<and>
    prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs"

inductive nsteps :: "nat \<Rightarrow> lan_cfg \<Rightarrow> observation list \<Rightarrow> lan_cfg \<Rightarrow> bool" where
  nsteps_refl: "nsteps 0 p [] p"
| nsteps_l: "\<lbrakk>step p1 \<kappa> p2; nsteps n p2 \<kappa>s p3\<rbrakk> \<Longrightarrow> nsteps (Suc n) p1 (\<kappa>@\<kappa>s) p3"

declare nsteps.intros[intro]
inductive_cases nstepsE[elim]: "nsteps 0 p \<kappa> q"
  "nsteps (Suc n) p \<kappa> q"

definition pure_step :: "expr \<Rightarrow> expr \<Rightarrow> bool" where
  "pure_step e1 e2 \<equiv> (\<forall>\<sigma>. reducible_no_obs e1 \<sigma>) \<and> 
    (\<forall>\<sigma>1 \<kappa> e2' \<sigma>2 efs. prim_step e1 \<sigma>1 \<kappa> e2' \<sigma>2 efs \<longrightarrow> \<kappa> = [] \<and> \<sigma>2 = \<sigma>1 \<and> e2' = e2 \<and> efs = [])"

definition pure_head_step :: "expr \<Rightarrow> expr \<Rightarrow> bool" where
  "pure_head_step e1 e2 \<equiv> (\<forall>\<sigma>. head_red_no_obs e1 \<sigma>) \<and> 
    (\<forall>\<sigma>1 \<kappa> e2' \<sigma>2 efs. head_step e1 \<sigma>1 \<kappa> e2' \<sigma>2 efs \<longrightarrow> \<kappa> = [] \<and> \<sigma>2 = \<sigma>1 \<and> e2' = e2 \<and> efs = [])"

lemma pure_head_step_pure_step: "pure_head_step e1 e2 \<Longrightarrow> pure_step e1 e2"
proof -
  assume assm: "pure_head_step e1 e2"
  then have no_obs: "head_red_no_obs e1 s" and 
    head_step: "head_step e1 s1 k e2' s2 efs \<Longrightarrow> k = [] \<and> s2 = s1 \<and> e2' = e2 \<and> efs = []"
    for s s1 k e2' s2 efs by (auto simp: pure_head_step_def)
  from no_obs have no_obs': "\<forall>s. reducible_no_obs e1 s" 
    apply (auto simp: reducible_no_obs_def head_red_no_obs_def )
    using prim_step_simp by blast
  from head_step[OF head_red_prim_step[OF head_red_no_obs_red[OF no_obs]]]
  show ?thesis by (auto simp: pure_step_def no_obs')
qed
  
abbreviation pure_exec :: "bool \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" where
  "pure_exec P n e1 e2 \<equiv> P \<longrightarrow> rel_nsteps pure_step n e1 e2"

lemma beta_red_no_obs: "head_red_no_obs (App (of_val (RecV f x e)) (of_val v)) \<sigma>"
  by (auto simp: head_red_no_obs_def intro!: prim_step_simp)

lemma pure_exec_beta: 
  "pure_exec True 1 (App (Val (RecV f x e)) (Val v)) (subst' x v (subst' f (RecV f x e) e))" 
  by (auto simp: pure_head_step_def beta_red_no_obs intro!: rel_one_step pure_head_step_pure_step)

lemma pure_exec_fst:
  "pure_exec True 1 (Fst (Val (PairV v1 v2))) (Val v1)"
  apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: rel_one_step pure_head_step_pure_step)
  by auto

lemma pure_exec_snd:
  "pure_exec True 1 (Snd (Val (PairV v1 v2))) (Val v2)"
  apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: rel_one_step pure_head_step_pure_step)
  by auto

lemma pure_exec_if_false: "pure_exec True 1 (If (Val (LitV (LitBool False))) e1 e2) (e2)"
  apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
  using IfFalseS by fastforce+

lemma pure_exec_if_true: "pure_exec True 1 (If (Val (LitV (LitBool True))) e1 e2) (e1)"
  apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
  using IfFalseS by fastforce+

lemma pure_exec_injl: "pure_exec True 1 (InjL (Val e)) (InjLV e)"
apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
  using InjLS by fastforce+

lemma pure_exec_injr: "pure_exec True 1 (InjR (Val e)) (InjRV e)"
apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
using InjRS by fastforce+

lemma pure_exec_case_injl: "pure_exec True 1 (Case (InjLV v) e1 e2) (App e1 (Val v))"
apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
using CaseLS by fastforce+

lemma pure_exec_case_injr: "pure_exec True 1 (Case (InjRV v) e1 e2) (App e2 (Val v))"
apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
using CaseLS by fastforce+

lemma pure_exec_pair: "pure_exec True 1 (Pair (Val v1) (Val v2)) (PairV v1 v2)"
apply (auto simp: pure_head_step_def head_red_no_obs_def intro!: pure_head_step_pure_step rel_one_step)
using CaseLS by fastforce+

text \<open>Atomicity proofs, but mostly axiomatized.\<close>
    
lemma atomic_rec [atomic_rule,log_prog_rule]: "atomic a (Rec f x e)" 
proof (auto simp: atomic_def prim_step_def)
  fix \<sigma> \<kappa> \<sigma>' efs K e1' e2'
  assume assms: "Rec f x e = fill K e1'" "e1' \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2' \<sigma>' efs"
  from fill_Rec[OF assms(1)[symmetric]] have K: "K = []" "e1' = Rec f x e" by simp_all
  with assms(2) have "\<kappa>=[]" "e2' = Val(RecV f x e)" "efs = []" by auto
  with K have "fill K e2' = Val(RecV f x e)" unfolding fill_def by simp
  then show "case a of StronglyAtomic \<Rightarrow> \<exists>v. to_val (fill K e2') = Some v | WeaklyAtomic \<Rightarrow> irreducible (fill K e2') \<sigma>'"
  by (cases a) (auto simp: irred_val)
qed

lemma atomic_pair [atomic_rule,log_prog_rule]: "atomic a (Pair (Val v1) (Val v2))" sorry
lemma atomic_injl [atomic_rule,log_prog_rule]: "atomic a (InjL (Val v))" sorry
lemma atomic_injr [atomic_rule,log_prog_rule]: "atomic a (InjR (Val v))" sorry
lemma atomic_beta [atomic_rule,log_prog_rule]: "atomic a (App (RecV f x (Val v1)) (Val v2))" sorry
lemma atomic_unop [atomic_rule,log_prog_rule]: "atomic a (UnOp uop (Val v))" sorry
lemma atomic_binop [atomic_rule,log_prog_rule]: "atomic a (BinOp bop (Val v1) (Val v2))" sorry
lemma atomic_if_true [atomic_rule,log_prog_rule]: "atomic a (If (Val (LitV (LitBool True))) (Val v1) e2)" sorry
lemma atomic_if_false [atomic_rule,log_prog_rule]: "atomic a (If (Val (LitV (LitBool False))) e1 (Val v2))" sorry
lemma atomic_fst [atomic_rule,log_prog_rule]: "atomic a (Fst (Val v))" sorry
lemma atomic_snd [atomic_rule,log_prog_rule]: "atomic a (Snd (Val v))" sorry
lemma atomic_fork [atomic_rule,log_prog_rule]: "atomic a (Fork e)" sorry
lemma atomic_alloc [atomic_rule,log_prog_rule]: "atomic a (AllocN (Val v1) (Val v2))" sorry
lemma atomic_free [atomic_rule,log_prog_rule]: "atomic a (Free (Val v))" sorry
lemma atomic_load [atomic_rule,log_prog_rule]: "atomic a (Load (Val v))" sorry
lemma atomic_xchg [atomic_rule,log_prog_rule]: "atomic a (Xchg (Val v1) (Val v2))" sorry

lemma atomic_store [atomic_rule,log_prog_rule]: "atomic a (Store (Val v1) (Val v2))"
proof (auto simp: atomic_def prim_step_def)
  fix \<sigma> \<kappa> \<sigma>' efs K e1' e2'
  assume assms: "Store (of_val v1) (of_val v2) = fill K e1'" "e1' \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2' \<sigma>' efs"
  with fill_store_val have K: "K=[]" "e1' = Store (Val v1) (Val v2)" by auto
  with assms(2) have " e2' = (Val (LitV LitUnit))" by auto
  with K show "case a of StronglyAtomic \<Rightarrow> \<exists>v. to_val (fill K e2') = Some v | WeaklyAtomic \<Rightarrow> irreducible (fill K e2') \<sigma>'"
    by (cases a, auto simp: fill_def irred_val)
qed
  
lemma atomic_cmp_xchg [atomic_rule,log_prog_rule]: "atomic a (CmpXchg (Val v0) (Val v1) (Val v2))" sorry
lemma atomic_faa [atomic_rule,log_prog_rule]: "atomic a (FAA (Val v1) (Val v2))" sorry
lemma atomic_new_proph [atomic_rule,log_prog_rule]: "atomic a NewProph" sorry
lemma atomic_resolve [atomic_rule,log_prog_rule]: "atomic a e \<Longrightarrow> atomic a (Resolve e (Val v1) (Val v2))" sorry


lemma fill_item_aux: "fill K e = e2 \<Longrightarrow> e2 = lang_ctxt (F K) e" by simp

method subst_fill_expr for K :: "ectx_item list" and orig e :: expr =
  match (K) in "[]" \<Rightarrow> succeed \<bar> _ \<Rightarrow> \<open>subst fill_item_aux[of K e orig], simp add: fill_def\<close>

method go for K :: "ectx_item list" and orig e :: expr = match (e) in 
  "App e1 (Val v)" for e1 and v \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "AppLCtx v # K" orig e1\<close>\<close>
\<bar> "App e1 e2" for e1 e2 :: expr \<Rightarrow> \<open>go "AppRCtx e1 # K" orig e2\<close>
\<bar> "UnOp op e1" for op and e1 \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "UnOpCtx op # K" orig e1\<close>\<close>
\<bar> "BinOp op e1 (Val v)" for op e1 v \<Rightarrow>
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "BinOpLCtx op v # K" orig e1\<close>\<close>
\<bar> "BinOp op e1 e2" for op e1 e2 \<Rightarrow> \<open>go "BinOpRCtx op e1 # K" orig e2\<close>
\<bar> "If e0 e1 e2" for e0 e1 e2 \<Rightarrow> 
  \<open>match (e0) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "IfCtx e1 e2 # K" orig e0\<close>\<close>
\<bar> "Pair e1 (Val v)" for e1 v \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "PairLCtx v # K" orig e1\<close>\<close>
\<bar> "Pair e1 e2" for e1 e2 \<Rightarrow> \<open>go "PairRCtx e1 # K" orig e2\<close>
\<bar> "Fst e1" for e1 \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "FstCtx # K" orig e1\<close>\<close>
\<bar> "Snd e1" for e1 \<Rightarrow>
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "SndCtx # K" orig e1\<close>\<close>
\<bar> "InjL e1" for e1 \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "InjLCtx # K" orig e1\<close>\<close>
\<bar> "InjR e1" for e1 \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "InjRCtx # K" orig e1\<close>\<close>
\<bar> "Case e0 e1 e2" for e0 e1 e2 \<Rightarrow> 
  \<open>match (e0) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "CaseCtx e1 e2 # K" orig e0\<close>\<close>
\<bar> "AllocN e1 (Val v)" for e1 v \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "AllocNLCtx v # K" orig e1\<close>\<close>
\<bar> "AllocN e1 e2" for e1 e2 \<Rightarrow> \<open>go "AllocNRCtx e1 # K" orig e2\<close>
\<bar> "Free e1" for e1 \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "FreeCtx # K" orig e1\<close>\<close>
\<bar> "Load e1" for e1 \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "LoadCtx # K" orig e1\<close>\<close>
\<bar> "Store e1 (Val v)" for e1 v \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "StoreLCtx v # K" orig e1\<close>\<close>
\<bar> "Store e1 e2" for e1 e2 \<Rightarrow> \<open>go "StoreRCtx e1 # K" orig e2\<close>
\<bar> "Xchg e1 (Val v)" for e1 v \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "XchgLCtx v # K" orig e1\<close>\<close>
\<bar> "Xchg e1 e2" for e1 e2 \<Rightarrow> \<open>go "XchgRCtx e1 # K" orig e2\<close>
\<bar> "CmpXchg e1 (Val v1) (Val v2)" for e1 v1 v2 \<Rightarrow> 
  \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> \<bar> _ \<Rightarrow> \<open>go "CmpXchgLCtx v1 v2 # K" orig e1\<close>\<close>
\<bar> "CmpXchg e0 e1 (Val v)" for e0 e1 v \<Rightarrow> \<open>go "CmpXchgMCtx e0 v # K" orig e1\<close> 
\<bar> "CmpXchg e0 e1 e2" for e0 e1 e2 \<Rightarrow> \<open>go "CmpXchgRCtx e0 e1 # K" orig e2\<close>
\<bar> "FAA e1 (Val v)" for e1 v \<Rightarrow> \<open>match (e1) in "Val _" \<Rightarrow> \<open>subst_fill_expr K orig e\<close> 
  \<bar> _ \<Rightarrow> \<open>go "FaaLCtx v # K" orig e1\<close>\<close>
\<bar> "FAA e1 e2" for e1 e2 \<Rightarrow> \<open>go "FaaRCtx e1 # K" orig e1\<close>
\<bar> "Resolve _ _ _" \<Rightarrow> fail
\<bar> _ \<Rightarrow> \<open>subst_fill_expr K orig e\<close>

method reshape_expr for e :: expr = (go "[]" e e)
end