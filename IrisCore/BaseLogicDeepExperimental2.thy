theory BaseLogicDeepExperimental2
imports CoreStructures Namespace "../HeapLang/State"
begin

text \<open> An experimental approach to a deep embedding of the Iris base/core logic.\<close>

text \<open>Deep embedding of camera objects\<close>
datatype 'a cmra_term = ConstC 'a | Core \<open>'a cmra_term\<close> | Op \<open>'a cmra_term\<close> \<open>'a cmra_term\<close>

text \<open>Deep embedding of step-index predicates about camera objects\<close>
datatype 'a cmra_atom = 
  Own \<open>'a cmra_term\<close> \<comment> \<open>Holds for camera objects which include the given partial resource\<close>
| Valid \<open>'a cmra_term\<close>

datatype quantifier_type = Name name | Expr expr | State state | List \<open>quantifier_type list\<close>
  | Observation observation

abbreviation "uname n \<equiv> case n of Name n \<Rightarrow> n"
abbreviation "uexpr e \<equiv> case e of Expr e \<Rightarrow> e"
abbreviation "ustate s \<equiv> case s of State s \<Rightarrow> s"
abbreviation "ulist f l \<equiv> case l of List l \<Rightarrow> map f l"
abbreviation "uobs ob \<equiv> case ob of Observation ob \<Rightarrow> ob"

datatype 'a cmra_pred = 
  Atom \<open>'a cmra_atom\<close> \<comment> \<open>An atomic predicate about camera resources\<close>
  \<comment> \<open>Standard separation logic connectives\<close>
| Sep \<open>'a cmra_pred\<close> \<open>'a cmra_pred\<close> \<comment> \<open>Separating conjunction\<close>
| Wand \<open>'a cmra_pred\<close> \<open>'a cmra_pred\<close> \<comment> \<open>Wand combinator, i.e. resource specific implication\<close>
| Pure \<open>bool\<close> \<comment> \<open>Wrapper for pure Isabelle/HOL propositions\<close>
  \<comment> \<open>Iris specific modalities\<close>
| Persistent \<open>'a cmra_pred\<close> \<comment> \<open>Predicate holds for core of the camera argument\<close>
| Plain \<open>'a cmra_pred\<close> \<comment> \<open>Predicate holds for unit camera object\<close>
| Later \<open>'a cmra_pred\<close> \<comment> \<open>Increases step index by one (also holds for n=0)\<close>
| BUpd \<open>'a cmra_pred\<close> \<comment> \<open>Predicate holds after one frame-preserving update\<close>
  \<comment> \<open>Standard logic connectives\<close>
| Impl \<open>'a cmra_pred\<close> \<open>'a cmra_pred\<close> 
| Conj \<open>'a cmra_pred\<close> \<open>'a cmra_pred\<close>
| Disj \<open>'a cmra_pred\<close> \<open>'a cmra_pred\<close>
  \<comment> \<open>Quantifiers\<close>
| Exists \<open>quantifier_type \<Rightarrow> 'a cmra_pred\<close> (binder "\<exists>\<^sub>u" 15)
| Forall \<open>quantifier_type \<Rightarrow> 'a cmra_pred\<close> (binder "\<forall>\<^sub>u" 15)

term \<open>TYPE('a)\<close>

fun cmra_eval :: "'a::ucamera cmra_term \<Rightarrow> 'a" where
  "cmra_eval (ConstC a) = a"
| "cmra_eval (Core a) = core (cmra_eval a)"
| "cmra_eval (Op a b) = (cmra_eval a) \<cdot> (cmra_eval b)"

type_synonym 'a upred = "'a \<Rightarrow> nat \<Rightarrow> bool"

fun atom_sem :: "'a::ucamera cmra_atom \<Rightarrow> 'a upred" where
  "atom_sem (Own a) b n = n_incl n (cmra_eval a) b"
| "atom_sem (Valid a) _ n = n_valid (cmra_eval a) n"

function pred_sem :: "'a::ucamera cmra_pred \<Rightarrow> 'a upred" where
  "pred_sem (Atom a) b n = atom_sem a b n"
| "pred_sem (Sep P Q) a n = (\<exists>b1 b2. n_equiv n a (b1 \<cdot> b2) \<and> pred_sem P b1 n \<and> pred_sem Q b2 n)"
| "pred_sem (Wand P Q) a n = 
  (\<forall>m b. m\<le>n \<and> n_valid (a \<cdot> b) m \<longrightarrow> pred_sem P b m \<longrightarrow> pred_sem Q (a \<cdot> b) m)"
| "pred_sem (Pure b) _ _ = b"
| "pred_sem (Persistent P) a n = pred_sem P (core a) n"
| "pred_sem (Plain P) a n = pred_sem P \<epsilon> n"
| "pred_sem (Later P) a n = (n=0 \<or> pred_sem P a (n-1))"
| "pred_sem (BUpd P) a n = 
  (\<forall>m a'. m\<le>n \<and> n_valid (a \<cdot> a') m \<longrightarrow> (\<exists>b. n_valid (b \<cdot> a') m \<and> pred_sem P b m))"
| "pred_sem (Impl P Q) a n = 
  (\<forall>m b. m\<le>n \<and> incl a b \<and> n_valid b m \<longrightarrow> pred_sem P b m \<longrightarrow> pred_sem Q b m)"
| "pred_sem (Conj P Q) a n = (pred_sem P a n \<and> pred_sem Q a n)"
| "pred_sem (Disj P Q) a n = (pred_sem P a n \<or> pred_sem Q a n)"
| "pred_sem (Exists P) a n = (\<exists>x. pred_sem (P x) a n)"
| "pred_sem (Forall P) a n = (\<forall>x. pred_sem (P x) a n)"
apply auto using cmra_pred.exhaust by blast

definition upred_entails :: "'a::ucamera upred \<Rightarrow> 'a upred \<Rightarrow> bool" where
  "upred_entails P Q \<equiv> \<forall>a n. n_valid a n \<longrightarrow> P a n \<longrightarrow> Q a n"
definition pred_entails :: "'a::ucamera cmra_pred \<Rightarrow> 'a cmra_pred \<Rightarrow> bool" where
  "pred_entails P Q = upred_entails (pred_sem P) (pred_sem Q)"  
  
definition upred_holds :: "'a::ucamera upred \<Rightarrow> bool" where
  "upred_holds P \<equiv> \<forall>a n. n_valid a n \<longrightarrow>  P a n"
definition pred_holds :: "'a::ucamera cmra_pred \<Rightarrow> bool" where
  "pred_holds P = upred_holds (pred_sem P)"
end