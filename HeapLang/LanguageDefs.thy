theory LanguageDefs
imports PrimitiveLaws State "../IrisCore/AuthHeap" "../IrisCore/Invariant"
begin

text \<open>Auxiliary language specific definitions\<close>

definition state_interp :: "state \<Rightarrow> observation list \<Rightarrow> iprop" where
  "state_interp \<sigma> \<kappa>s = heap_interp (heap \<sigma>) \<^emph> proph_map_interp \<kappa>s (used_proph_id \<sigma>)"

definition fill :: "ectx_item list \<Rightarrow> expr \<Rightarrow> expr"  where "fill K e =  fold fill_item K e"

lemma fill_item_Rec: "fill_item K' e2 \<noteq> Rec f x e" by (induction K') auto
lemma fill_Rec: "fill K e' = Rec f x e \<Longrightarrow> K =[] \<and> e' = Rec f x e"
  apply (induction K arbitrary: e') apply (auto simp: fill_def) using fill_item_Rec by blast

lemma fill_item_Val: "fill_item K e \<noteq> Val v" by (induction K) auto
lemma fill_Val: "fill K e = Val v \<Longrightarrow> K = [] \<and> e = Val v"
  apply (induction K arbitrary: e) apply (auto simp: fill_def) using fill_item_Val by blast

datatype langCtxt = FI ectx_item | F "ectx_item list"
fun lang_ctxt :: "langCtxt \<Rightarrow> expr \<Rightarrow> expr" where
  "lang_ctxt (FI K) e = fill_item K e"
| "lang_ctxt (F K) e = fill K e"
  
definition prim_step :: "expr \<Rightarrow> state \<Rightarrow> observation list \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> bool" where
  "prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs \<equiv> \<exists>K e1' e2'. ((e1=fill K e1') \<and> (e2=fill K e2') \<and> head_step e1' \<sigma>1 \<kappa> e2' \<sigma>2 efs)"

lemma prim_step_simp: "head_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs \<Longrightarrow> prim_step e1 \<sigma>1 \<kappa> e2 \<sigma>2 efs"
  unfolding prim_step_def fill_def by (metis fold_simps(1))

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
  
text \<open>Atomicity proofs, but mostly axiomatized.\<close>
    
lemma atomic_rec [atomic_rule]: "atomic a (Rec f x e)" 
proof (auto simp: atomic_def prim_step_def)
  fix \<sigma> \<kappa> \<sigma>' efs K e1' e2'
  assume assms: "Rec f x e = fill K e1'" "e1' \<sigma> \<kappa> \<Rightarrow>\<^sub>h e2' \<sigma>' efs"
  from fill_Rec[OF assms(1)[symmetric]] have K: "K = []" "e1' = Rec f x e" by simp_all
  with assms(2) have "\<kappa>=[]" "e2' = Val(RecV f x e)" "efs = []" by auto
  with K have "fill K e2' = Val(RecV f x e)" unfolding fill_def by simp
  then show "case a of StronglyAtomic \<Rightarrow> \<exists>v. to_val (fill K e2') = Some v | WeaklyAtomic \<Rightarrow> irreducible (fill K e2') \<sigma>'"
  by (cases a) (auto simp: irred_val)
qed

lemma atomic_pair [atomic_rule]: "atomic a (Pair (Val v1) (Val v2))" sorry
lemma atomic_injl [atomic_rule]: "atomic a (InjL (Val v))" sorry
lemma atomic_injr [atomic_rule]: "atomic a (InjR (Val v))" sorry
lemma atomic_beta [atomic_rule]: "atomic a (App (RecV f x (Val v1)) (Val v2))" sorry
lemma atomic_unop [atomic_rule]: "atomic a (UnOp uop (Val v))" sorry
lemma atomic_binop [atomic_rule]: "atomic a (BinOp bop (Val v1) (Val v2))" sorry
lemma atomic_if_true [atomic_rule]: "atomic a (If (Val (LitV (LitBool True))) (Val v1) e2)" sorry
lemma atomic_if_false [atomic_rule]: "atomic a (If (Val (LitV (LitBool False))) e1 (Val v2))" sorry
lemma atomic_fst [atomic_rule]: "atomic a (Fst (Val v))" sorry
lemma atomic_snd [atomic_rule]: "atomic a (Snd (Val v))" sorry
lemma atomic_fork [atomic_rule]: "atomic a (Fork e)" sorry
lemma atomic_alloc [atomic_rule]: "atomic a (AllocN (Val v1) (Val v2))" sorry
lemma atomic_free [atomic_rule]: "atomic a (Free (Val v))" sorry
lemma atomic_load [atomic_rule]: "atomic a (Load (Val v))" sorry
lemma atomic_xchg [atomic_rule]: "atomic a (Xchg (Val v1) (Val v2))" sorry
lemma atomic_store [atomic_rule]: "atomic a (Store (Val v1) (Val v2))" sorry
lemma atomic_cmp_xchg [atomic_rule]: "atomic a (CmpXchg (Val v0) (Val v1) (Val v2))" sorry
lemma atomic_faa [atomic_rule]: "atomic a (FAA (Val v1) (Val v2))" sorry
lemma atomic_new_proph [atomic_rule]: "atomic a NewProph" sorry
lemma atomic_resolve [atomic_rule]: "atomic a e \<Longrightarrow> atomic a (Resolve e (Val v1) (Val v2))" sorry
end