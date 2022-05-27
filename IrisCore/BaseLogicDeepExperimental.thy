theory BaseLogicDeepExperimental
imports CoreStructures Namespace "../HeapLang/PrimitiveLaws" Frac DerivedConstructions
  "../SpanningTree/SpanningTreeCameras" "../HeapLang/State"
begin

text \<open> An experimental approach to a deep embedding of the Iris base/core logic.\<close>

text \<open>Deep embedding of camera objects\<close>
datatype 'a cmra_term = ConstC 'a | Core \<open>'a cmra_term\<close> | Op \<open>'a cmra_term\<close> \<open>'a cmra_term\<close>

text \<open>Deep embedding of step-index predicates about camera objects\<close>
datatype 'a cmra_atom = 
  Own \<open>'a cmra_term\<close> \<comment> \<open>Holds for camera objects which include the given partial resource\<close>
| Valid \<open>'a cmra_term\<close>

text \<open>Predicate connectives\<close>
datatype 'a iprop = 
  Atom \<open>'a cmra_atom\<close> \<comment> \<open>An atomic predicate about camera resources\<close>
  \<comment> \<open>Standard separation logic connectives\<close>
| Sep "'a iprop" "'a iprop" \<comment> \<open>Separating conjunction\<close>
| Wand "'a iprop" "'a iprop" \<comment> \<open>Wand combinator, i.e. resource specific implication\<close>
| Pure bool \<comment> \<open>Wrapper for pure Isabelle/HOL propositions\<close>
  \<comment> \<open>Iris specific modalities\<close>
| Persistent "'a iprop" \<comment> \<open>Predicate holds for core of the camera argument\<close>
| Plain "'a iprop" \<comment> \<open>Predicate holds for unit camera object\<close>
| Later "'a iprop" \<comment> \<open>Increases step index by one (also holds for n=0)\<close>
| BUpd "'a iprop" \<comment> \<open>Predicate holds after one frame-preserving update\<close>
  \<comment> \<open>Standard logic connectives\<close>
| Impl "'a iprop" "'a iprop"
| Conj "'a iprop" "'a iprop"
| Disj "'a iprop" "'a iprop"

datatype 'a inv = Inv \<open>(name, 'a res iprop later) map_view \<times> name dset \<times> name dfset\<close>
  and 'a res = Res "(gname \<rightharpoonup> 'a inv) \<times> 'a"

definition "invariant_name :: gname \<equiv> 1" 
definition "enabled_name :: gname \<equiv> 2" 
definition "disabled_name :: gname \<equiv> 3"

fun get_inv :: "gname \<Rightarrow> 'a res \<Rightarrow> 'a inv option" where "get_inv \<gamma> (Res (i,a)) = i \<gamma>"
definition constr_inv :: "gname \<Rightarrow> 'a::ucamera inv \<Rightarrow> 'a res" where
  "constr_inv \<gamma> i = Res ([\<gamma>\<mapsto>i],\<epsilon>)"
 
instance inv :: (type) ucamera sorry
instance res :: (type) ucamera sorry
instance iprop :: (type) ofe sorry

type_synonym 'a atom = "'a cmra_atom"

primrec cmra_eval :: "'a::ucamera cmra_term \<Rightarrow> 'a" where
  "cmra_eval (ConstC a) = a"
| "cmra_eval (Core a) = core (cmra_eval a)"
| "cmra_eval (Op a b) = (cmra_eval a) \<cdot> (cmra_eval b)"

type_synonym 'a upred = "'a \<Rightarrow> nat \<Rightarrow> bool"

primrec atom_sem :: "'a::ucamera atom \<Rightarrow> 'a upred" where
  "atom_sem (Own a) b n = n_incl n (cmra_eval a) b"
| "atom_sem (Valid a) _ n = n_valid (cmra_eval a) n"

fun pred_sem :: "'a::ucamera iprop \<Rightarrow> 'a upred"
where
  "pred_sem (Atom a) = (\<lambda>b n. atom_sem a b n)"
| "pred_sem (Sep P Q) = (\<lambda>a n. (\<exists>b1 b2. n_equiv n a (b1 \<cdot> b2) \<and> pred_sem P b1 n \<and> pred_sem Q b2 n))"
| "pred_sem (Wand P Q) = (\<lambda>a n.
  (\<forall>m b. m\<le>n \<and> n_valid (a \<cdot> b) m \<longrightarrow> pred_sem P b m \<longrightarrow> pred_sem Q (a \<cdot> b) m))"
| "pred_sem (Pure b) = (\<lambda>_ _.  b)"
| "pred_sem (Persistent P) = (\<lambda>a n. pred_sem P (core a) n)"
| "pred_sem (Plain P) = (\<lambda>_ n. pred_sem P \<epsilon> n)"
| "pred_sem (Later P) = (\<lambda>a n. (n=0 \<or> pred_sem P a (n-1)))"
| "pred_sem (BUpd P) = (\<lambda>a n.
  (\<forall>m a'. m\<le>n \<and> n_valid (a \<cdot> a') m \<longrightarrow> (\<exists>b. n_valid (b \<cdot> a') m \<and> pred_sem P b m)))"
| "pred_sem (Impl P Q) = (\<lambda>a n.
  (\<forall>m b. m\<le>n \<and> incl a b \<and> n_valid b m \<longrightarrow> pred_sem P b m \<longrightarrow> pred_sem Q b m))"
| "pred_sem (Conj P Q) = (\<lambda>a n. (pred_sem P a n \<and> pred_sem Q a n))"
| "pred_sem (Disj P Q) = (\<lambda>a n. (pred_sem P a n \<or> pred_sem Q a n))"
  
definition uniform :: "'a::ucamera upred \<Rightarrow> bool" where
  "uniform f \<longleftrightarrow> (\<forall>n m x y. f x n \<longrightarrow> n_incl m x y \<longrightarrow> m\<le>n \<longrightarrow> f y m)"

lemma upred_weaken: "\<lbrakk>n_equiv n x y; m\<le>n;uniform f; f x n\<rbrakk> \<Longrightarrow> f y m"
  using total_n_inclI uniform_def by fast

lemma upred_weaken_simple: "\<lbrakk>uniform f; f x n; m\<le>n\<rbrakk> \<Longrightarrow> f x m"
  using ofe_refl upred_weaken by blast
  
lemma atom_sem_uniform: "uniform (atom_sem a)"
proof (induct a)
  case (Own x)
  then show ?case unfolding uniform_def n_incl_def atom_sem.simps
  using camera_assoc op_equiv_subst by (metis (no_types, lifting))
next
  case (Valid x)
  then show ?case by (simp add: uniform_def)
qed

lemma pred_sem_uniform: "uniform (pred_sem P)"
proof (induct P rule: iprop.induct)
  case (Atom x)
  then show ?case by (simp) (rule atom_sem_uniform)
next
  case (Sep P Q)
  then have Q: "\<And>n m x y. \<lbrakk>(pred_sem Q) x n; n_incl m x y; m\<le>n\<rbrakk> \<Longrightarrow> (pred_sem Q) y m"
    by (auto simp: uniform_def)
  {
    fix n m x y
    assume assms: "pred_sem (Sep P Q) x n" "n_incl m x y" "m\<le>n"
    then obtain b1 b2 where bs: "n_equiv n x (b1 \<cdot> b2)" "(pred_sem P) b1 n" "(pred_sem Q) b2 n"
      by auto
    from assms(2) obtain z where z: "n_equiv m y (x \<cdot> z)" by (auto simp: n_incl_def)
    from op_equiv_subst[OF this bs(1) assms(3)] camera_assoc have "n_equiv m y (b1 \<cdot> (b2 \<cdot> z))" 
      by (metis (no_types, lifting))
    with upred_weaken_simple[OF Sep(1) bs(2) assms(3)] Q[OF bs(3) n_incl_op_extend assms(3), of z]
    have "pred_sem (Sep P Q) y m" unfolding pred_sem.simps by blast
  }
  then show ?case by (simp add: uniform_def)
next
  case (Wand P Q)
  then have Q: "\<And>n m x y. \<lbrakk>(pred_sem Q) x n; n_incl m x y; m\<le>n\<rbrakk> \<Longrightarrow> (pred_sem Q) y m"
    by (auto simp: uniform_def)
  {
    fix n m x y
    assume assms: "pred_sem (Wand P Q) x n" "n_incl m x y" "m\<le>n"
    then have I: "\<And>m b. \<lbrakk>m\<le>n; n_valid (x \<cdot> b) m; (pred_sem P) b m\<rbrakk> \<Longrightarrow> (pred_sem Q) (x \<cdot> b) m" 
      by auto
    {
      fix m' z
      assume assms2: "m'\<le>m" "n_valid (y \<cdot> z) m'" "(pred_sem P) z m'"
      from assms(3) assms2(1) have "m'\<le>n" by linarith
      from Q[OF I[OF this n_valid_incl_subst[OF assms(2) assms2(2,1)] assms2(3)] 
        n_incl_extend[OF assms(2) assms2(1), of z] order.refl]
      have "(pred_sem Q) (y \<cdot> z) m'" .
    }
    then have "pred_sem (Wand P Q) y m" by simp
  }
  then show ?case by (simp add: uniform_def)
next
  case (Pure b)  
  then show ?case by (simp add: uniform_def)
next
  case (Persistent P)
  {
    fix n m x y
    assume assms: "pred_sem (Persistent P) x n" "n_incl m x y" "m\<le>n"
    then have I: "pred_sem P (core x) n" by simp
    from assms(2) have "n_incl m (core x) (core y)" by (rule camera_core_mono_n)
    with Persistent I assms(3) have "pred_sem (Persistent P) y m" 
      unfolding pred_sem.simps uniform_def by blast
  }
  then show ?case by (simp add: uniform_def)
next
  case (Plain P)
  then show ?case by (simp add: uniform_def)
next
  case (Later P)
  then show ?case by (auto simp: uniform_def camera_n_incl_le diff_le_mono) 
next
  case (BUpd P)
  then show ?case by (simp add: uniform_def n_valid_incl_subst order.trans)
next
  case (Impl P Q)
  then have P: "\<And>n m x y. \<lbrakk>(pred_sem P) x n; n_incl m x y; m\<le>n\<rbrakk> \<Longrightarrow> (pred_sem P) y m"
    by (auto simp: uniform_def)
  from Impl(2) have Q: "\<And>n m x y. \<lbrakk>(pred_sem Q) x n; n_incl m x y; m\<le>n\<rbrakk> \<Longrightarrow> (pred_sem Q) y m"
    by (auto simp: uniform_def)  
  {
    fix n m x y
    assume assms: "pred_sem (Impl P Q) x n" "n_incl m x y" "m\<le>n"
    then have I: "\<And>m' z. \<lbrakk>m'\<le>n;incl x z; n_valid z m'; pred_sem P z m'\<rbrakk> \<Longrightarrow> pred_sem Q z m'"
      by auto
    {
      fix m' z
      assume assms2: "m'\<le>m" "incl y z" "n_valid z m'" "pred_sem P z m'"
      with assms(3) have "m'\<le>n" by linarith
      from assms(2) obtain y' where y': "n_equiv m y (x\<cdot>y')" using n_incl_def by blast
      with ofe_sym ofe_mono[OF assms2(1)] have y'_sym: "n_equiv m' (x\<cdot>y') y" by fast
      from assms2(2) obtain z' where z': "z=y\<cdot>z'" using incl_def by blast
      from valid_op_op_weaken[OF ofe_mono[OF assms2(1) y'] assms2(3)[simplified this]] 
        have "n_valid ((x\<cdot>y')\<cdot>z') m'" .
      moreover have "incl x ((x\<cdot>y')\<cdot>z')" using incl_op_extend incl_def by blast
      moreover from P[OF assms2(4) _ order.refl, simplified z', OF total_n_incl_extend[OF y' assms2(1)]]
        have "pred_sem P ((x\<cdot>y')\<cdot>z') m'".
      ultimately have "pred_sem Q ((x\<cdot>y')\<cdot>z') m'" using I[OF \<open>m'\<le>n\<close>] by simp
      from Q[OF this, of m' z, simplified z', OF total_n_incl_extend[OF y'_sym order.refl] order.refl] 
      have "pred_sem Q z m'" unfolding z' .
    }
    then have "pred_sem (Impl P Q) y m" by (simp add: uniform_def)
  }
  then show ?case using uniform_def by blast
next
  case (Conj P Q)
  then show ?case by (auto simp: uniform_def)
next
  case (Disj P Q)
  then show ?case by (auto simp: uniform_def)
qed

context assumes "SORT_CONSTRAINT('a::ucamera)" begin

definition upred_entails :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> bool" where
  "upred_entails P Q \<equiv> \<forall>a n. n_valid a n \<longrightarrow> P a n \<longrightarrow> Q a n"
definition pred_entails :: "'a iprop \<Rightarrow> 'a iprop \<Rightarrow> bool" where
  "pred_entails P Q = upred_entails (pred_sem P) (pred_sem Q)"  
  
definition upred_holds :: "'a upred \<Rightarrow> bool" where
  "upred_holds P \<equiv> \<forall>a n. n_valid a n \<longrightarrow>  P a n"
definition pred_holds :: "'a iprop \<Rightarrow> bool" where
  "pred_holds P = upred_holds (pred_sem P)"
end

context assumes "SORT_CONSTRAINT('a::ucamera)" begin
definition own_inv :: "gname \<Rightarrow> 'a inv \<Rightarrow> 'a res iprop" where
  "own_inv \<gamma> i = Atom (Own(ConstC (constr_inv \<gamma> i)))"

definition sep_map_set :: "('b\<Rightarrow>'a res iprop) \<Rightarrow> 'b set \<Rightarrow> 'a res iprop" where
  "sep_map_set f s = folding_on.F (\<lambda>x a. Sep a (f x)) (Pure True) s"

definition ownI :: "name \<Rightarrow> 'a res iprop \<Rightarrow> 'a res iprop" where
  "ownI \<iota> P = own_inv invariant_name (Inv (view_frag [\<iota>\<mapsto>(DfracDiscarded,to_ag (Next P))],\<epsilon>,\<epsilon>))"

definition inv :: "namespace \<Rightarrow> 'a res iprop \<Rightarrow> 'a res iprop" where
  "inv N P = Pure (\<exists> \<iota>. pred_holds (Conj (Pure (\<iota>\<in>names N)) ((ownI \<iota> P))))"
  
definition ownE :: "name set \<Rightarrow> 'a res iprop" where
  "ownE E = own_inv enabled_name (Inv (\<epsilon>,DSet E,\<epsilon>))"

definition ownD :: "name fset \<Rightarrow> 'a res iprop" where
  "ownD D = own_inv disabled_name (Inv (\<epsilon>,\<epsilon>,DFSet D))"
  
definition lift_inv_fmap :: "(name,'a res iprop) fmap \<Rightarrow> (name,'a res iprop later) fmap" where
  "lift_inv_fmap m = Abs_fmap (map_option Next \<circ> (fmlookup m))"

definition wsat :: "'a res iprop" where
  "wsat \<equiv> Pure (\<exists>(I::(name,'a res iprop) fmap). pred_holds
    (Sep (own_inv invariant_name (Inv(view_auth_full(lift_inv_fmap I),\<epsilon>,\<epsilon>)))
     (sep_map_set (\<lambda>\<iota>. Disj (Sep (Later((the \<circ> (fmlookup I)) \<iota>)) (ownD {|\<iota>|}))
      (ownE {\<iota>})) (fmdom' I))))"
end
      
context
fixes get_heap :: "gname \<Rightarrow> 'a::ucamera res \<Rightarrow> heap_lang_heap option"
  and constr_heap :: "gname \<Rightarrow> heap_lang_heap \<Rightarrow> 'a res"
assumes inG_heap: "inG get_heap constr_heap"
begin

definition heap_name :: gname where "heap_name = 42"

abbreviation own_heap :: "heap_lang_heap \<Rightarrow> 'a res iprop" where
  "own_heap h \<equiv> Atom (Own (ConstC (constr_heap heap_name h)))"

definition points_to :: "loc \<Rightarrow> dfrac \<Rightarrow> val \<Rightarrow> 'a res iprop" where
  "points_to l dq v = own_heap(view_frag [l\<mapsto>(dq, to_ag (Some v))])"
abbreviation points_to_disc :: "loc \<Rightarrow> val \<Rightarrow> 'a res iprop" where 
  "points_to_disc \<equiv> \<lambda>l v. points_to l DfracDiscarded v"
abbreviation points_to_own :: "loc \<Rightarrow> frac \<Rightarrow> val \<Rightarrow> 'a res iprop" where
  "points_to_own \<equiv> \<lambda>l p v. points_to l (DfracOwn p) v"
abbreviation points_to_full :: "loc \<Rightarrow> val \<Rightarrow> 'a res iprop" where
  "points_to_full \<equiv> \<lambda>l v. points_to_own l 1 v"

definition own_state_heap :: "state \<Rightarrow> 'a res iprop" where
  "own_state_heap s = own_heap (view_auth_full (heap s))"
end

type_synonym res1 = "(gname \<rightharpoonup> heap_lang_heap) res"

fun get_heap :: "gname \<Rightarrow> res1 \<Rightarrow> heap_lang_heap option" where
  "get_heap \<gamma> (Res (_,h)) = h \<gamma>"
definition constr_heap :: "gname \<Rightarrow> heap_lang_heap \<Rightarrow> res1" where
  "constr_heap \<gamma> h = Res (\<epsilon>, [\<gamma>\<mapsto>h])"

lemma res_n_equiv: "n_equiv n (Res r1) (Res r2) \<longleftrightarrow> n_equiv n r1 r2" sorry
lemma res_valid: "n_valid (Res r) n \<longleftrightarrow> n_valid r n" sorry
lemma res_pcore: "pcore (Res r) = map_option Res (pcore r)" sorry
lemma res_\<epsilon>: "\<epsilon> = Res \<epsilon>" sorry
lemma res_op: "Res r1 \<cdot> Res r2 = Res (r1\<cdot>r2)" sorry

interpretation inG_heap: inG get_heap constr_heap 
apply (auto simp: inG_def constr_heap_def non_expansive_def res_n_equiv res_valid prod_n_valid_def \<epsilon>_n_valid res_pcore
  pcore_prod_def \<epsilon>_pcore pcore_fun_alt ofe_refl  res_\<epsilon> res_op op_prod_def \<epsilon>_left_id
  split: option.splits)
by (auto simp: \<epsilon>_fun_def \<epsilon>_option_def)


lemma ownE_singleton_twice: "pred_entails (Sep (ownE {i}) (ownE {i})) (Pure False)"
apply (auto simp: pred_entails_def upred_entails_def ownE_def own_inv_def constr_inv_def n_incl_def)
subgoal for a n b1 b2 c d
apply (cases c; cases d; cases b1; cases b2)
apply (auto simp: res_n_equiv res_op op_prod_def \<epsilon>_left_id op_fun_def op_option_def n_equiv_fun_def
  n_equiv_option_def split: option.splits)
sorry
done
end