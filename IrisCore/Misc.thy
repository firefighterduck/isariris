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
end