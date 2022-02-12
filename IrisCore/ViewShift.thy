theory ViewShift
imports Invariant
begin

subsubsection \<open>Fancy updates\<close>

type_synonym mask = "name dset"

definition fancy_upd :: "mask \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("\<Turnstile>{_,_}=>_") where
  "\<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>P \<equiv> (wsat \<^emph> ownE \<E>\<^sub>1) -\<^emph> (\<Rrightarrow>\<^sub>b (\<diamondop> (wsat \<^emph> ownE \<E>\<^sub>2 \<^emph> P)))"
abbreviation wand_fupd ("_={_,_}=\<^emph>_") where "wand_fupd P \<E>\<^sub>1 \<E>\<^sub>2 Q \<equiv> P -\<^emph> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>Q"
  
abbreviation linear_fupd :: "mask \<Rightarrow> iprop \<Rightarrow> iprop" ("\<Turnstile>{_}=>_") where 
  "linear_fupd \<E> P \<equiv> \<Turnstile>{\<E>,\<E>}=>P"
abbreviation wand_linear_fupd ("_={_}=\<^emph>_") where "wand_linear_fupd P \<E> Q \<equiv> P -\<^emph> \<Turnstile>{\<E>}=>Q"

definition view_shift :: "iprop \<Rightarrow> mask \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("_ ={_,_}=>_")  where
  "view_shift P \<E>\<^sub>1 \<E>\<^sub>2 Q = \<box>(P -\<^emph> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>Q)"
abbreviation linear_vs :: "iprop \<Rightarrow> mask \<Rightarrow> iprop \<Rightarrow> iprop" ("_ ={_}=>_") where
  "linear_vs P \<E> Q \<equiv> P ={\<E>,\<E>}=> Q"
  
lemma fupd_mono: "P\<turnstile>Q \<Longrightarrow> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>P \<turnstile> \<Turnstile>{\<E>\<^sub>1, \<E>\<^sub>2}=>Q"
unfolding fancy_upd_def
apply (rule upred_wandI)
unfolding wsat_def ownE_def ownD_def sep_map_set_def except_zero_def
sorry

text \<open>Semantic invariant definition\<close>
definition sinv :: "namespace \<Rightarrow> iprop \<Rightarrow> iprop" where
  "sinv N P = \<box>(\<forall>\<^sub>u E. ((\<upharpoonleft>((dnames N) \<subseteq>\<^sub>d E)) \<longrightarrow>\<^sub>u 
    ((\<Turnstile>{E,E-(dnames N)}=> (\<triangleright>P)) \<^emph> ((\<triangleright>P) ={E-(dnames N), E}=\<^emph> \<upharpoonleft>True))))"

lemma inv_acc: "dnames N \<subseteq>\<^sub>d E \<Longrightarrow> 
  upred_holds (((inv N P) ={E, E-(dnames N)}=\<^emph> (\<triangleright>P)) \<^emph> ((\<triangleright>P) ={E-(dnames N), E}=\<^emph> \<upharpoonleft>True))"
unfolding fancy_upd_def inv_def upred_holds.rep_eq
sorry

lemma fresh_inv_name: "\<exists>\<iota>. \<not> (\<iota> \<in>\<^sub>f E) \<and> \<iota> \<in>\<^sub>d dnames N"
proof -
  from infinite_names dset_of_finite_finite have "dnames N - dset_of_finite E \<noteq> DSet {}"
    unfolding dnames_def apply (cases E) apply auto using finite_fset infinite_super apply blast 
    using not_no_names by simp
  then obtain \<iota> where "\<iota> \<in>\<^sub>d dnames N - dset_of_finite E" unfolding dnames_def by (cases E) auto
  then have "\<not> (\<iota> \<in>\<^sub>f E) \<and> \<iota> \<in>\<^sub>d dnames N" apply (cases E) by (auto simp add: dnames_def fmember.rep_eq)
  then show ?thesis by blast
qed

lemma inv_alloc: "upred_holds ((\<triangleright>P) ={E}=\<^emph> (inv N P))"
unfolding fancy_upd_def
sorry
end