theory COFEs
imports NonExpansive
begin

subsection \<open> COFE \<close>
typedef (overloaded) 't chain = "{c::(nat \<Rightarrow> 't::ofe). \<forall>n m. n\<le>m \<longrightarrow> n_equiv n (c m) (c n)}"
  using ofe_eq_limit by force
setup_lifting type_definition_chain
lemmas [simp] = Rep_chain_inverse Rep_chain_inject
lemmas [simp, intro!] = Rep_chain[unfolded mem_Collect_eq]

class cofe = ofe +
  fixes lim :: "('a::ofe) chain \<Rightarrow> 'a"
  assumes core_compl: "n_equiv n (lim c) (Rep_chain c n)"

definition discrete_lim :: "('a::discrete chain) \<Rightarrow> 'a" where
  "discrete_lim c = Rep_chain c 0"

lemma discrete_cofe: "n_equiv n (discrete_lim c) (Rep_chain c n)"
  unfolding discrete_lim_def by transfer (metis d_equiv nat_le_linear)

subsubsection \<open>Banach's fixed-point\<close>

definition fixpoint_chain :: "('a::ofe,'a) contr \<Rightarrow> 'a chain" where
  "fixpoint_chain f = Abs_chain (\<lambda>n. Nat.compower (Rep_contr f) (Suc n) (SOME (x::'a). True))"

definition fixpoint :: "('a::cofe,'a) contr \<Rightarrow> 'a" where
  "fixpoint f = lim (fixpoint_chain f)"

lemma fp_chain:"(\<lambda>n. Nat.compower (Rep_contr (f::('a::cofe,'a) contr)) (Suc n) x) \<in>
  {c. \<forall>n m. n\<le>m \<longrightarrow> n_equiv n (c m) (c n)}"
  apply auto apply transfer 
  subgoal for n m f x
proof (induction n arbitrary: m)
  case 0
  then show ?case by (auto intro: contractiveE)
next
  case (Suc n)
  then have "n \<le> (m-1)" by simp
  then obtain m' where m': "m' = m-1" by simp
  then have f_m': "f ((f^^m') x) = (f^^m) x" apply auto
    by (metis One_nat_def Suc.prems(1) Suc_le_D comp_def diff_Suc_1 funpow.simps(2))
  from m' \<open>n\<le>(m-1)\<close> have "n\<le>m'" by simp
  show ?case apply (rule contractive_Suc[OF Suc(3)])
  using Suc(1)[OF \<open>n\<le>m'\<close> Suc(3)] by (auto simp: f_m')
qed
done

lemma fixpoint_unfold: "ofe_eq (fixpoint f) (Rep_contr f (fixpoint f))" 
apply (auto simp: ofe_limit fixpoint_def)
subgoal for n
apply (induction n)
subgoal
  apply (subst ofe_trans_eqL[OF core_compl])
  apply (auto simp: fixpoint_chain_def Abs_chain_inverse[OF fp_chain, simplified])
  using Rep_contr contractive_zero by blast
subgoal for n'
  unfolding ofe_trans_eqL[OF core_compl]
  apply (auto simp: fixpoint_chain_def Abs_chain_inverse[OF fp_chain, simplified])
  by (auto simp: ofe_trans_eqR[OF core_compl] Abs_chain_inverse[OF fp_chain, simplified] ofe_refl
    intro!: contractive_Suc[of "Rep_contr f"])
  done
done

lemma banachs_fixes_point2: "ofe_eq x (Rep_contr f x) \<Longrightarrow> ofe_eq x (fixpoint f)"
apply (auto simp: ofe_limit)
subgoal for n
proof (induction n)
  case 0
  then have x0: "n_equiv 0 x (Rep_contr f x)" by simp
  show ?case 
    by (auto simp: fixpoint_def fixpoint_chain_def ofe_trans_eqR[OF core_compl] 
      Abs_chain_inverse[OF fp_chain, simplified] ofe_trans_eqL[OF x0] intro:
      contractive_zero)
next
  case (Suc n)
  then have IH: "n_equiv n x (fixpoint f)" by simp
  from Suc(2) have x_Sn: "n_equiv (Suc n) x (Rep_contr f x)" by simp
  show ?case apply (auto simp: ofe_trans_eqL[OF x_Sn] ofe_trans_eqR[OF ofe_eq_equiv[OF fixpoint_unfold]])
  apply (rule contractive_Suc[of "Rep_contr f"])
  by (auto simp: IH)
qed
done

subsection \<open>COFE instances\<close>

subsubsection \<open>Unit type cofe\<close>
instantiation unit :: cofe begin
definition lim_unit :: "unit chain \<Rightarrow> unit" where [simp]: "lim_unit _ = ()"
instance by standard (simp add: n_equiv_unit_def)
end

subsubsection \<open>Option type cofe\<close>
lift_definition option_chain :: "'a::ofe option chain \<Rightarrow> 'a \<Rightarrow> 'a chain" is
  "\<lambda>c x n. case c n of Some y \<Rightarrow> y | None \<Rightarrow> x" 
  by (auto simp: ofe_refl n_equiv_option_def split: option.splits) fastforce+

instantiation option :: (cofe) cofe begin
definition lim_option :: "'a option chain \<Rightarrow> 'a option" where
  "lim_option c \<equiv> case (Rep_chain c 0) of Some x \<Rightarrow> Some (lim (option_chain c x)) | None \<Rightarrow> None"
instance proof
  fix c :: "'a option chain" and n
  have base: "n_equiv 0 (Rep_chain c n) (Rep_chain c 0)" by transfer auto
  from core_compl have step: "n_equiv n (lim (option_chain c x)) (Rep_chain (option_chain c x) n)" for x .
  show "n_equiv n (lim c) (Rep_chain c n)" unfolding lim_option_def
  apply (cases "Rep_chain c 0")
  apply simp_all
  apply (metis base n_equiv_option_def option.distinct(1))
  by (smt (verit) base step n_equiv_option_def option.simps(5) option_chain.rep_eq)
qed
end

subsubsection \<open>Later type ofe\<close>
lift_definition later_chain :: "'a::ofe later chain \<Rightarrow> 'a chain" is
  "\<lambda>c n. later_car (Rep_chain c (Suc n))" 
  by transfer (metis Suc_le_mono add_diff_cancel_left' n_equiv_later_def nat.discI plus_1_eq_Suc)

instantiation later :: (cofe) cofe begin
definition lim_later :: "'a later chain \<Rightarrow> 'a later" where
  "lim_later c = Next (lim (later_chain c))"
instance proof
  fix c :: "'a later chain" and n
  from core_compl[of n] show "n_equiv n (lim c) (Rep_chain c n)" 
    apply (simp add: n_equiv_later_def lim_later_def)
    by (smt (verit, ccfv_threshold) Suc_pred bot_nat_0.not_eq_extremum core_compl later_chain.rep_eq)
qed
end

subsubsection \<open>Product type COFE\<close>
lift_definition chain_map :: "('a::ofe -n> 'b::ofe) \<Rightarrow> 'a chain \<Rightarrow> 'b chain" is
  "\<lambda>f c n. f (Rep_chain c n)" by transfer (simp add: non_expansive_def)

lift_definition ne_fst :: "('a::ofe\<times>'b::ofe)-n>'a" is "\<lambda>(a,_). a" by (rule non_expansiveI) auto
lift_definition ne_snd :: "('a::ofe\<times>'b::ofe)-n>'b" is "\<lambda>(_,b). b" by (rule non_expansiveI) auto

instantiation prod :: (cofe,cofe) cofe begin
definition lim_prod :: "('a \<times> 'b) chain \<Rightarrow> 'a \<times> 'b" where 
  "lim_prod c = (lim (chain_map ne_fst c), lim (chain_map ne_snd c))"
instance proof 
  fix c :: "('a\<times>'b) chain" and n
  have "n_equiv n (lim (chain_map ne_fst c)) (Rep_chain (chain_map ne_fst c) n)" 
    "n_equiv n (lim (chain_map ne_snd c)) (Rep_chain (chain_map ne_snd c) n)" 
    using core_compl by auto  
  then show "n_equiv n (lim c) (Rep_chain c n)"
  apply (simp add: lim_prod_def ne_fst.rep_eq ne_snd.rep_eq chain_map_def)
  by (smt (z3) Abs_chain_inverse Rep_chain case_prod_conv mem_Collect_eq n_equiv_prod.elims(2) n_equiv_prod.elims(3))
qed
end

subsubsection \<open>Non expansive function COFE\<close>
lift_definition ne_chain :: "('a::ofe,'b::ofe) ne chain \<Rightarrow> 'a \<Rightarrow> 'b chain" is
  "\<lambda>c x n. Rep_ne (c n) x" apply transfer unfolding non_expansive_def by auto
  
instantiation ne :: (ofe,cofe) cofe begin
lift_definition lim_ne :: "('a, 'b) ne chain \<Rightarrow> ('a, 'b) ne" is
  "\<lambda>c x. lim (ne_chain c x)"
  by (metis (no_types, lifting) Rep_ne core_compl mem_Collect_eq ne_chain.rep_eq non_expansive_def 
    ofe_sym ofe_trans)
instance apply standard apply (simp add: n_equiv_ne_def lim_ne.rep_eq ne_chain_def)
  by (smt (verit, best) Abs_chain_inverse Rep_chain core_compl mem_Collect_eq ne_chain.rep_eq)
end

end