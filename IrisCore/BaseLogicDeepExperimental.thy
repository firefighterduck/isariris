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

type_synonym 'a res = "(graphUR auth \<times> markingUR auth \<times> 'a \<times> heap_lang_heap)"

text \<open>Predicate connectives\<close>
datatype iprop = 
  Atom \<open>inv res cmra_atom\<close> \<comment> \<open>An atomic predicate about camera resources\<close>
  \<comment> \<open>Standard separation logic connectives\<close>
| Sep iprop iprop \<comment> \<open>Separating conjunction\<close>
| Wand iprop iprop \<comment> \<open>Wand combinator, i.e. resource specific implication\<close>
| Pure bool \<comment> \<open>Wrapper for pure Isabelle/HOL propositions\<close>
  \<comment> \<open>Iris specific modalities\<close>
| Persistent iprop \<comment> \<open>Predicate holds for core of the camera argument\<close>
| Plain iprop \<comment> \<open>Predicate holds for unit camera object\<close>
| Later iprop \<comment> \<open>Increases step index by one (also holds for n=0)\<close>
| BUpd iprop \<comment> \<open>Predicate holds after one frame-preserving update\<close>
  \<comment> \<open>Standard logic connectives\<close>
| Impl iprop iprop
| Conj iprop iprop
| Disj iprop iprop
  \<comment> \<open>Extensions that can not be defined without unfortunate complexity\<close>
| InvP namespace iprop
and inv = Inv \<open>(name\<rightharpoonup> iprop later ag) auth \<times> name dset \<times> name dfset\<close>

instance inv :: ucamera sorry
instance iprop :: ofe sorry

type_synonym atom = "inv res cmra_atom"

primrec cmra_eval :: "'a::ucamera cmra_term \<Rightarrow> 'a" where
  "cmra_eval (ConstC a) = a"
| "cmra_eval (Core a) = core (cmra_eval a)"
| "cmra_eval (Op a b) = (cmra_eval a) \<cdot> (cmra_eval b)"

type_synonym upred = "inv res \<Rightarrow> nat \<Rightarrow> bool"

primrec atom_sem :: "atom \<Rightarrow> upred" where
  "atom_sem (Own a) b n = n_incl n (cmra_eval a) b"
| "atom_sem (Valid a) _ n = n_valid (cmra_eval a) n"

fun pred_sem :: "iprop \<Rightarrow> upred" and inv_sem :: "inv \<Rightarrow> upred"
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
| "pred_sem (InvP N P) = (\<lambda>a n.
  (\<exists>\<iota>. \<iota> \<in> names N \<and> atom_sem (Own (ConstC (\<epsilon>,\<epsilon>,Inv (fragm [\<iota>\<mapsto>to_ag (Next P)],\<epsilon>,\<epsilon>),\<epsilon>))) a n))"
| "inv_sem (Inv _) _ _ = True"
  
definition uniform :: "upred \<Rightarrow> bool" where
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
proof (induct P rule: iprop.induct[of "\<lambda>_. True"])
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
next
  case (InvP N I)
  then show ?case unfolding pred_sem.simps uniform_def by (meson atom_sem_uniform uniform_def)
next
  case (Inv i)
  then show ?case by simp
qed

definition upred_entails :: "upred \<Rightarrow> upred \<Rightarrow> bool" where
  "upred_entails P Q \<equiv> \<forall>a n. n_valid a n \<longrightarrow> P a n \<longrightarrow> Q a n"
definition pred_entails :: "iprop \<Rightarrow> iprop \<Rightarrow> bool" where
  "pred_entails P Q = upred_entails (pred_sem P) (pred_sem Q)"  
  
definition upred_holds :: "upred \<Rightarrow> bool" where
  "upred_holds P \<equiv> \<forall>a n. n_valid a n \<longrightarrow>  P a n"
definition pred_holds :: "iprop \<Rightarrow> bool" where
  "pred_holds P = upred_holds (pred_sem P)"
end