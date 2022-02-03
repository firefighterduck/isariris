theory Misc
imports iPropShallow
begin

definition map_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<times>'v\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "map_heap h f a = folding_on.F f a {(l,v) |l v. h l = Some v}"

definition sep_map_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<times>'v\<Rightarrow>iprop) \<Rightarrow> iprop" where
  "sep_map_heap h f = map_heap h (\<lambda>lv a. a \<^emph> f lv) (\<upharpoonleft>True)"

definition sep_map_set :: "('b\<Rightarrow>iprop) \<Rightarrow> 'b set \<Rightarrow> iprop" where
  "sep_map_set f s = folding_on.F (\<lambda>x a. a \<^emph> f x) (\<upharpoonleft>True) s"

definition sep_map_fset :: "('b\<Rightarrow>iprop) \<Rightarrow> 'b fset \<Rightarrow> iprop" where
  "sep_map_fset f s = folding_on.F (\<lambda>x a. a \<^emph> f x) (\<upharpoonleft>True) (fset s)"
  
abbreviation sep_map_fmdom :: "('b\<Rightarrow>iprop) \<Rightarrow> ('b,'a) fmap \<Rightarrow> iprop" where
  "sep_map_fmdom f m \<equiv> sep_map_fset f (fmdom m)"
  
lemma sep_map_dom_delete: "fmlookup m i = Some x \<Longrightarrow> 
  sep_map_fmdom P m = P i \<^emph> sep_map_fmdom P (fmdrop i m)"
unfolding sep_map_set_def
proof -
  assume "fmlookup m i = Some x"
  then have i_fin: "i |\<in>| fmdom m" by (rule fmdomI)
  then have i_in: "i \<in> fset (fmdom m)" by (simp add: fmember.rep_eq)
  have fold_on: "folding_on UNIV (\<lambda>x a. a \<^emph> P x)" by standard (auto simp: comp_def upred_sep_comm2_eq)
  have "finite (fset (fmdom m))" by simp
  have drop_minus: "fmdom (fmdrop i m) = (fmdom m |-| {|i|})" by simp
  have "folding_on.F (\<lambda>x a. a \<^emph> P x) (\<upharpoonleft>True) (fset (fmdom m)) =
    folding_on.F (\<lambda>x a. a \<^emph> P x) (\<upharpoonleft>True) (fset (fmdom m |-| {|i|})) \<^emph> (P i)"
  using folding_on.remove[OF fold_on _ \<open>finite (fset (fmdom m))\<close> i_in, simplified] by auto
  with drop_minus have "folding_on.F (\<lambda>x a. a \<^emph> P x) (\<upharpoonleft>True) (fset (fmdom m)) =
    folding_on.F (\<lambda>x a. a \<^emph> P x) (\<upharpoonleft>True) (fset (fmdom (fmdrop i m))) \<^emph> (P i)" by simp
  then show "sep_map_fmdom P m = P i \<^emph> sep_map_fmdom P (fmdrop i m)" 
    using sep_map_fset_def upred_sep_comm by metis
qed
end