theory Misc
imports iPropShallow "HOL-Library.Multiset"
begin

definition map_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<times>'v\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "map_heap h f a = folding_on.F f a {(l,v) |l v. h l = Some v}"

definition sep_map_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<times>'v\<Rightarrow>iprop) \<Rightarrow> iprop" where
  "sep_map_heap h f = map_heap h (\<lambda>lv a. a \<^emph> f lv) upred_emp"

definition sep_map_fmap :: "('l,'v::ofe) fmap \<Rightarrow> (('l\<times>'v)\<Rightarrow>iprop) \<Rightarrow> iprop" where
  "sep_map_fmap m f =   map_heap (fmlookup m) (\<lambda>lv a. a \<^emph> f lv) upred_emp"
  
definition sep_map_set :: "('b\<Rightarrow>iprop) \<Rightarrow> 'b set \<Rightarrow> iprop" where
  "sep_map_set f s = folding_on.F (\<lambda>x a. a \<^emph> f x) upred_emp s"

abbreviation sep_emp_map_list :: "'a list \<Rightarrow> ('a \<Rightarrow> iprop) \<Rightarrow> iprop" ("[\<^emph>\<^sub>l:] _ _") where
  "sep_emp_map_list l f \<equiv> foldl (\<lambda>P x. P \<^emph> f x) upred_emp l"
  
abbreviation sep_emp_fold_list :: "iprop list \<Rightarrow> iprop" ("[\<^emph>\<^sub>l] _") where
  "sep_emp_fold_list l \<equiv> foldl (\<^emph>) upred_emp l"

abbreviation sep_fold_list :: "iprop \<Rightarrow> iprop list \<Rightarrow> iprop" ("[\<^emph>\<^sub>l _] _") where 
  "sep_fold_list acc l \<equiv> foldl (\<^emph>) acc l"
  
definition sep_fold_fset :: "('a \<Rightarrow> iprop) \<Rightarrow> 'a fset \<Rightarrow> iprop \<Rightarrow> iprop" ("[\<^emph>\<^sub>f] _ _ _") where
  "sep_fold_fset f s acc = ffold (\<lambda>x a. a \<^emph> f x) acc s"

abbreviation sep_map_fset :: "('b\<Rightarrow>iprop) \<Rightarrow> 'b fset \<Rightarrow> iprop" ("[\<^emph>\<^sub>m] _ _") where
  "sep_map_fset f s \<equiv> sep_fold_fset f s upred_emp"

abbreviation sep_map_fmdom :: "('b\<Rightarrow>iprop) \<Rightarrow> ('b,'a) fmap \<Rightarrow> iprop" where
  "sep_map_fmdom f m \<equiv> sep_map_fset f (fmdom m)"

abbreviation sep_fold_multiset :: "iprop multiset \<Rightarrow> iprop" ("[\<^emph>\<^sub>#] _") where
  "sep_fold_multiset m \<equiv> fold_mset (\<^emph>) upred_emp m"

abbreviation sep_map_multiset :: "iprop \<Rightarrow> iprop multiset \<Rightarrow> iprop" ("[\<^emph>\<^sub># _] _") where
  "sep_map_multiset acc m \<equiv> fold_mset (\<^emph>) acc m"

lemma sep_fold_ne [upred_ne_rule]: 
  "\<lbrakk>n_equiv n f g; n_equiv n acc1 acc2\<rbrakk> \<Longrightarrow> n_equiv n (foldl (\<lambda>P x. P \<^emph> f x) acc1 l) (foldl (\<lambda>P x. P \<^emph> g x) acc2 l)"
proof (induction l arbitrary: acc1 acc2)
  case Nil
  then show ?case by (simp add: ofe_refl)
next
  case (Cons a l)
  then have "n_equiv n (f a) (g a)" by (auto simp: n_equiv_fun_def)
  with Cons(3) have "n_equiv n (acc1 \<^emph> f a) (acc2 \<^emph> g a)" 
    by (auto intro: upred_ne_rule)
  from Cons(1)[OF Cons(2) this] show ?case by auto
qed

lemma sep_emp_map_list_entails:
  "\<lbrakk>\<And>x. f x \<turnstile> g x; acc1 \<turnstile> acc2\<rbrakk> \<Longrightarrow> (foldl (\<lambda>P x. P \<^emph> f x) acc1 l) \<turnstile> (foldl (\<lambda>P x. P \<^emph> g x) acc2 l)"
proof (induction l arbitrary: acc1 acc2)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  have "acc1 \<^emph> f a \<turnstile> acc2 \<^emph> g a" apply (rule upred_sep_mono)
    using Cons by auto
  from Cons(1)[OF Cons(2) this] show ?case by auto
qed

lemma fold_sep_end: "foldl (\<lambda>P x. P \<^emph> f x) acc (a#l) = (foldl (\<lambda>P x. P \<^emph> f x) acc l) \<^emph> (f a)"
  by (induction l arbitrary: acc) (auto simp: upred_sep_comm2_eq)

lemma fold_sep_end2: "foldl (\<lambda>P x. P \<^emph> f x \<^emph> g x) acc (a#l) = (foldl (\<lambda>P x. P \<^emph> f x \<^emph> g x) acc l) \<^emph> (f a) \<^emph> (g a)"
  apply (induction l arbitrary: acc) apply auto
  by (smt (verit, best) upred_sep_comm2_eq)

lemma sep_emp_map_list_intro: "\<box>(\<forall>\<^sub>u x. f x) \<turnstile> (foldl (\<lambda>P x. P \<^emph> f x) upred_emp l)"
  apply (induction l)
  unfolding fold_sep_end
  apply auto 
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF persistent_dupl]], pers_solver)
  apply (auto intro!: upred_sep_mono)
  subgoal for a
  by (auto intro!: upred_entails_trans[OF upred_persisE] upred_entails_trans[OF upred_forall_inst[of _ a]])
  done

lemma sep_emp_map_list_sep: "foldl (\<lambda>P x. P \<^emph> f x \<^emph> g x) upred_emp l \<stileturn>\<turnstile> foldl (\<lambda>P x. P \<^emph> f x) upred_emp l \<^emph>
  foldl (\<lambda>P x. P \<^emph> g x) upred_emp l"
  apply (induction l)
  unfolding fold_sep_end fold_sep_end2
  apply (auto simp: upred_entail_eq_def upred_true_sep)
  apply (smt (verit, del_insts) upred_frame upred_sep_assoc_eq upred_sep_comm2_eq)
  by (smt (verit, del_insts) upred_frame upred_sep_assoc_eq upred_sep_comm2_eq)
  
lemma sep_emp_map_list_entails': 
  "(\<box>(\<forall>\<^sub>u x. ((f x) -\<^emph> (g x)))) -\<^emph> (foldl (\<lambda>P x. P \<^emph> f x) upred_emp l) -\<^emph> (foldl (\<lambda>P x. P \<^emph> g x) upred_emp l)"
  apply (rule upred_wand_holdsI)
  apply (rule upred_entails_trans[OF sep_emp_map_list_intro,of _ l])
  apply (rule upred_wandI)
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF sep_emp_map_list_sep]])
  apply (induction l)
  unfolding fold_sep_end fold_sep_end2
  apply auto
  apply (rule upred_entails_trans[OF upred_sep_comm2R])
  apply (rule upred_entails_substE[OF upred_wand_apply, unfolded upred_sep_assoc_eq])
  by (auto intro: upred_frame)
  
lemma sep_comp_fun_commute: "comp_fun_commute (\<^emph>)"
  apply standard apply (simp add: comp_def)
  by (metis upred_sep_assoc_eq upred_sep_comm)

lemma sep_P_comp_fun_commute: "comp_fun_commute (\<lambda>x a. a \<^emph> P x)"
  apply standard apply (simp add: comp_def comp_fun_commute_def upred_sep_comm)
  by (metis (no_types, opaque_lifting) upred_sep_assoc_eq upred_sep_comm)

lemma sep_map_dom_delete: "fmlookup m i = Some x \<Longrightarrow> 
  sep_map_fmdom P m = P i \<^emph> sep_map_fmdom P (fmdrop i m)"
unfolding sep_map_set_def
proof -
  assume "fmlookup m i = Some x"
  then have i_fin: "i |\<in>| fmdom m" by (rule fmdomI)
  have drop_minus: "fmdom (fmdrop i m) = (fmdom m |-| {|i|})" by simp
  have "ffold (\<lambda>x a. a \<^emph> P x) upred_emp (fmdom m) =
    ffold (\<lambda>x a. a \<^emph> P x) upred_emp (fmdom m |-| {|i|}) \<^emph> (P i)"
  using comp_fun_commute.ffold_rec[OF sep_P_comp_fun_commute i_fin] .
  with drop_minus have "ffold (\<lambda>x a. a \<^emph> P x) (\<upharpoonleft>True) (fmdom m) =
    ffold (\<lambda>x a. a \<^emph> P x) upred_emp (fmdom (fmdrop i m)) \<^emph> (P i)" by simp
  then show "sep_map_fmdom P m = P i \<^emph> sep_map_fmdom P (fmdrop i m)" 
  unfolding sep_fold_fset_def using upred_sep_comm by auto
qed

inductive rel_nsteps :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  zero_steps: "rel_nsteps R 0 x x"
| rel_step: "\<lbrakk>R x y; rel_nsteps R n y z\<rbrakk> \<Longrightarrow> rel_nsteps R (Suc n) x z"

declare rel_nsteps.intros[intro]
inductive_cases rel_nstepsE[elim!]: "rel_nsteps R 0 x y"
  "rel_nsteps R (Suc n) x y"

lemma rel_one_step: "R x y \<Longrightarrow> rel_nsteps R (Suc 0) x y"
  by auto  

lemma timeless_sep_map_fset [timeless_rule,log_prog_rule]: "(\<And>x. timeless (f x)) \<Longrightarrow> timeless ([\<^emph>\<^sub>m] f s)"
unfolding sep_fold_fset_def
apply (induction s)
apply (auto simp: comp_fun_commute.ffold_empty[OF sep_P_comp_fun_commute])
apply timeless_solver
apply (auto simp: comp_fun_commute.ffold_finsert[OF sep_P_comp_fun_commute])
by (timeless_solver; auto)

lemma sep_map_fset_insert: "fmlookup m i = None \<Longrightarrow> 
  [\<^emph>\<^sub>m] (\<lambda>(l,y). P l y) (fset_of_fmap (fmupd i x m)) \<stileturn>\<turnstile> P i x \<^emph> [\<^emph>\<^sub>m] (\<lambda>(l,y). P l y) (fset_of_fmap m)"
proof -
  assume assm: "fmlookup m i = None"
  then have fset_upd: "fset_of_fmap (fmupd i x m) = {|(i,x)|} |\<union>| fset_of_fmap m"
    apply (auto simp: fset_of_fmap.rep_eq) apply argo by (metis option.inject)
  from assm have "(i,x) |\<notin>| fset_of_fmap m" by simp
  show ?thesis 
  by (auto simp: sep_fold_fset_def fset_upd comp_fun_commute.ffold_finsert[OF 
    sep_P_comp_fun_commute \<open>(i,x) |\<notin>| fset_of_fmap m\<close>] upred_sep_comm split: prod.splits)
qed
end