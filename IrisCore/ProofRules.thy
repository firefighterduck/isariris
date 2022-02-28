theory ProofRules
imports BaseLogicShallow "HOL-Eisbach.Eisbach"
begin
subsubsection \<open> Basic properties of and proof rules for upred predicates. \<close>

lemma upred_entail_eq_simp: "P\<stileturn>\<turnstile>Q \<equiv> \<forall>a n. n_valid a n \<longrightarrow> Rep_upred_f P a n = Rep_upred_f Q a n"
  by (auto simp: upred_entail_eq_def upred_entails.rep_eq) (smt (verit, best))
lemma upred_entail_eqE: "P\<stileturn>\<turnstile>Q \<Longrightarrow> (\<And>a n. n_valid a n \<Longrightarrow> Rep_upred_f P a n = Rep_upred_f Q a n)"
  using upred_entail_eq_simp by auto
lemma upred_entail_eqI: "(\<And>a n. n_valid a n \<Longrightarrow> Rep_upred_f P a n = Rep_upred_f Q a n) \<Longrightarrow> P\<stileturn>\<turnstile>Q"
  using upred_entail_eq_simp by auto

lemma upred_entail_eq_symm: "P\<stileturn>\<turnstile>Q \<Longrightarrow> Q\<stileturn>\<turnstile>P"
  by (auto simp: upred_entail_eq_def)
  
lemma upred_entail_eqL: "P\<stileturn>\<turnstile>Q \<Longrightarrow> P\<turnstile>Q" by (simp add: upred_entail_eq_def)
lemma upred_entail_eqR: "P\<stileturn>\<turnstile>Q \<Longrightarrow> Q\<turnstile>P" by (simp add: upred_entail_eq_def)

lemma upred_entails_trans: "\<lbrakk>P\<turnstile>Q; Q\<turnstile>R\<rbrakk> \<Longrightarrow> P\<turnstile>R"
  by (auto simp: upred_entails.rep_eq)

lemma upred_weakeningL: "P\<^emph>Q \<turnstile> P"
  apply transfer using n_incl_def by blast

lemma upred_weakeningR: "P\<^emph>Q \<turnstile> Q"
  by transfer (metis camera_comm le_refl n_incl_def)

lemma upred_weakeningL': "P\<and>\<^sub>uQ \<turnstile> P"
  by transfer blast

lemma upred_weakeningR': "P\<and>\<^sub>uQ \<turnstile> Q"
  by transfer blast
  
lemma upred_weakeningR2: "P\<^emph>Q\<^emph>R\<turnstile>Q\<^emph>R"
  by transfer (metis camera_comm le_refl n_incl_def)

lemma upred_entails_add: "\<lbrakk>P\<turnstile>Q; P\<and>\<^sub>uQ\<turnstile>R\<rbrakk> \<Longrightarrow> P\<turnstile>R"
  by transfer blast  

lemma upred_entails_conjI: "\<lbrakk>P\<turnstile>Q; P\<turnstile>R\<rbrakk> \<Longrightarrow> P \<turnstile> Q \<and>\<^sub>u R"
  by transfer blast
lemma upred_entails_conj_sep: "P \<^emph> Q \<turnstile> P \<and>\<^sub>u Q"
  by transfer (metis camera_comm le_refl n_incl_def)

lemma upred_impl_apply: "P \<and>\<^sub>u (P\<longrightarrow>\<^sub>uQ) \<turnstile> Q"
  by transfer (metis \<epsilon>_right_id incl_def order_refl)

lemma upred_disjE: "\<lbrakk>P\<turnstile>R; Q\<turnstile>R\<rbrakk> \<Longrightarrow> P\<or>\<^sub>uQ\<turnstile>R"
  by transfer' blast
lemma upred_disjE': "\<lbrakk>P\<^emph>Q\<turnstile>T; P\<^emph>R\<turnstile>T\<rbrakk> \<Longrightarrow> P\<^emph>(Q\<or>\<^sub>uR)\<turnstile>T"
  by transfer' blast
lemma upred_disjIL: "P\<turnstile>Q \<Longrightarrow> P\<turnstile>Q\<or>\<^sub>uR"
  by transfer blast
lemma upred_disjIR: "P\<turnstile>R \<Longrightarrow> P\<turnstile>Q\<or>\<^sub>uR"
  by transfer blast
  
lemma upred_entails_refl [simp]: "P\<turnstile>P" by (auto simp: upred_entails_def)
lemma upred_entail_eq_refl [simp]: "P \<stileturn>\<turnstile> P" by (auto simp: upred_entail_eq_def)

lemma upred_entails_eq: "P=Q \<Longrightarrow> P\<turnstile>Q" by simp
lemma upred_entails_eq_eq: "P=Q \<Longrightarrow> P\<stileturn>\<turnstile>Q" using upred_entails_eq upred_entail_eq_def by blast

lemma own_valid: "Own(a) \<turnstile> \<V>(a)"
  unfolding upred_entails.rep_eq upred_own.rep_eq upred_valid.rep_eq n_incl_def
  using camera_valid_op n_valid_ne by blast

lemma upred_holds_entails: "upred_holds P \<longleftrightarrow> ((upred_emp) \<turnstile> P)"
  by (auto simp: upred_holds.rep_eq upred_entails.rep_eq upred_pure.rep_eq)
lemma upred_holds_entails': "upred_holds P \<Longrightarrow> P \<turnstile> upred_emp"
  by (simp add: upred_entails.rep_eq upred_pure.rep_eq)

lemma upred_emp_entailed [simp]: "P \<turnstile> upred_emp" by transfer simp
  
lemma upred_entailsE: "P \<turnstile> Q \<Longrightarrow> (\<And>a n. \<lbrakk>n_valid a n; Rep_upred_f P a n\<rbrakk> \<Longrightarrow> Rep_upred_f Q a n)"
  by (auto simp: upred_entails.rep_eq)

lemma upred_entailsI: "(\<And>a n. \<lbrakk>n_valid a n; Rep_upred_f P a n\<rbrakk> \<Longrightarrow> Rep_upred_f Q a n) \<Longrightarrow> P \<turnstile> Q"
  by (auto simp: upred_entails.rep_eq)
  
lemma upred_wandI: "(P \<^emph> Q) \<turnstile> R \<Longrightarrow> P \<turnstile> (Q-\<^emph>R)"
  unfolding upred_entails.rep_eq upred_sep.rep_eq upred_wand.rep_eq
  using ofe_refl upred_def_rep upred_weaken_simple by blast
lemma upred_wandE: "P \<turnstile> (Q-\<^emph>R) \<Longrightarrow> (P \<^emph> Q) \<turnstile> R"
  by transfer (meson camera_valid_op dual_order.refl n_valid_ne ofe_sym total_n_inclI)
lemma upred_wand_apply: "P\<^emph>(P-\<^emph>Q) \<turnstile> Q"
  by transfer (metis camera_comm n_valid_ne ofe_sym order_refl total_n_inclI)

lemma upred_wand_apply': "P\<turnstile>Q \<Longrightarrow> P\<^emph>(Q-\<^emph>R)\<turnstile>R"
  by transfer (metis camera_comm camera_valid_op n_valid_ne ofe_sym order_refl total_n_inclI)

lemma upred_true_sep: "(P \<^emph> upred_emp) = P"
  apply transfer using n_incl_def by fastforce

lemma upred_true_conj: "(P \<and>\<^sub>u upred_emp) = P" 
  by transfer simp

lemma upred_true_conj': "(upred_emp \<and>\<^sub>u P) = P" 
  by transfer simp

lemma upred_true_wand: "(upred_emp -\<^emph> P) \<turnstile> P"
  by transfer (metis \<epsilon>_right_id order_refl)

lemma upred_conj_comm: "P \<and>\<^sub>u Q = Q \<and>\<^sub>u P"
  by transfer fast  

lemma upred_conj_comm2R: "P \<and>\<^sub>u Q \<and>\<^sub>u R = P \<and>\<^sub>u R \<and>\<^sub>u Q"
  by transfer fast
  
lemma upred_conj_assoc: "P \<and>\<^sub>u (Q \<and>\<^sub>u R) = P \<and>\<^sub>u Q \<and>\<^sub>u R"
  by transfer blast

lemma upred_sep_comm: "P \<^emph> Q = Q \<^emph> P"
  by transfer (metis (no_types, opaque_lifting) camera_comm)

lemma upred_sep_assoc: "P \<^emph> (Q \<^emph> R) \<turnstile> (P \<^emph> Q) \<^emph> R"
proof (rule upred_entailsI)
  fix a n
  assume "n_valid a n" "Rep_upred_f (P \<^emph> (Q \<^emph> R)) a n"
  then have "\<exists>b1 b2. n_equiv n a (b1 \<cdot> b2) \<and> Rep_upred_f P b1 n \<and> Rep_upred_f (Q \<^emph> R) b2 n"
    using upred_sep.rep_eq by metis
  then obtain b1 b2 where b: "n_equiv n a (b1 \<cdot> b2) \<and> Rep_upred_f P b1 n \<and> Rep_upred_f (Q \<^emph> R) b2 n"
    by blast  
  then have "\<exists>c1 c2. n_equiv n b2 (c1 \<cdot> c2) \<and> Rep_upred_f Q c1 n \<and> Rep_upred_f R c2 n"
    using upred_sep.rep_eq by metis
  then obtain c1 c2 where c: "n_equiv n b2 (c1 \<cdot> c2) \<and> Rep_upred_f Q c1 n \<and> Rep_upred_f R c2 n" by blast
  with b have a:"n_equiv n a (b1 \<cdot> c1 \<cdot> c2)" by (metis camera_assoc ofe_refl ofe_trans op_equiv)
  from b c have "n_equiv n (b1 \<cdot> c1) (b1 \<cdot> c1) \<and> Rep_upred_f P b1 n \<and> Rep_upred_f Q c1 n"
    using ofe_refl by blast
  then have "Rep_upred_f (P \<^emph> Q) (b1 \<cdot> c1) n" using upred_sep.rep_eq by metis
  with a c have "n_equiv n a ((b1 \<cdot> c1) \<cdot> c2) \<and> Rep_upred_f (P \<^emph> Q) (b1 \<cdot> c1) n \<and> Rep_upred_f R c2 n"
    by blast    
  then show "Rep_upred_f ((P \<^emph> Q) \<^emph> R) a n" using upred_sep.rep_eq by metis
qed

lemma upred_sep_assoc_rev: "(P \<^emph> Q) \<^emph> R \<turnstile> P \<^emph> (Q \<^emph> R)"
  by (metis upred_sep_assoc upred_sep_comm)

lemma upred_sep_assoc': "P \<^emph> (Q \<^emph> R) \<^emph> T \<turnstile> (P \<^emph> Q) \<^emph> R \<^emph> T"
  using upred_sep_assoc by (metis upred_entails.rep_eq upred_entailsE upred_wandE upred_wandI)

lemma upred_sep_assoc'_rev: "(P \<^emph> Q) \<^emph> R \<^emph> T \<turnstile> P \<^emph> (Q \<^emph> R) \<^emph> T"
  by (metis upred_sep_assoc' upred_sep_comm)  
  
lemma upred_sep_comm2L: "P \<^emph> Q \<^emph> R = Q \<^emph> P \<^emph> R"
using upred_sep_comm by metis

lemma upred_sep_comm2R: "P \<^emph> Q \<^emph> R \<turnstile> P \<^emph> R \<^emph> Q"
apply transfer'
apply auto
by (metis camera_assoc camera_comm le_refl ofe_refl op_equiv_subst)

lemma upred_sep_comm2_eq: "P \<^emph> Q \<^emph> R = P \<^emph> R \<^emph> Q"
apply transfer'
apply (auto simp: fun_eq_iff)
apply (metis camera_assoc camera_comm ofe_refl op_equiv_subst order_refl)
by (metis camera_assoc camera_comm ofe_refl op_equiv_subst order_refl)

lemma upred_sep_comm3M: "P \<^emph> Q \<^emph> R \<^emph> T \<turnstile> P \<^emph> R \<^emph> Q \<^emph> T"
  using upred_sep_comm2R
  by (smt (verit, ccfv_SIG) upred_entails_trans upred_wandE upred_wandI)

lemma upred_sep_comm3L: "P \<^emph> Q \<^emph> R \<^emph> T \<turnstile> Q \<^emph> P \<^emph> R \<^emph> T"
  by (simp add: upred_sep_comm)  

lemma upred_sep_comm4_2: "P \<^emph> Q \<^emph> R \<^emph> T \<^emph> S \<turnstile> P \<^emph> R \<^emph> Q \<^emph> T \<^emph> S"
  by (simp add: upred_sep_comm2_eq)

lemma upred_sep_comm4_1: "P \<^emph> Q \<^emph> R \<^emph> T \<^emph> S \<turnstile> Q \<^emph> P \<^emph> R \<^emph> T \<^emph> S"
  by (simp add: upred_sep_comm)

lemma upred_sep_comm5_2: "P \<^emph> Q \<^emph> R \<^emph> T \<^emph> S \<^emph> U \<turnstile> P \<^emph> R \<^emph> Q \<^emph> T \<^emph> S \<^emph> U"
  by (simp add: upred_sep_comm2_eq)

lemma upred_sep_comm5_1: "P \<^emph> Q \<^emph> R \<^emph> T \<^emph> S \<^emph> U \<turnstile> Q \<^emph> P \<^emph> R \<^emph> T \<^emph> S \<^emph> U"
  by (simp add: upred_sep_comm)

lemma upred_sep_comm6_2: "P \<^emph> Q \<^emph> R \<^emph> T \<^emph> S \<^emph> U \<^emph> V \<turnstile> P \<^emph> R \<^emph> Q \<^emph> T \<^emph> S \<^emph> U \<^emph> V"
  by (simp add: upred_sep_comm2_eq)

lemma upred_sep_comm6_1: "P \<^emph> Q \<^emph> R \<^emph> T \<^emph> S \<^emph> U \<^emph> V \<turnstile> Q \<^emph> P \<^emph> R \<^emph> T \<^emph> S \<^emph> U \<^emph> V"
  by (simp add: upred_sep_comm)
  
lemma upred_sep_comm6_2R: "P \<^emph> Q \<^emph> R \<^emph> S \<^emph> T \<^emph> U \<^emph> V \<turnstile> P \<^emph> R \<^emph> S \<^emph> T \<^emph> U \<^emph> V \<^emph> Q"
  by (auto simp: upred_sep_comm2_eq)

lemma upred_sep_assoc_eq: "P \<^emph> (Q \<^emph> R) = P \<^emph> Q \<^emph> R"
  by (metis upred_sep_comm upred_sep_comm2_eq)
  
lemma upred_sep_mono: "\<lbrakk>P1\<turnstile>Q;P2\<turnstile>R\<rbrakk> \<Longrightarrow> P1\<^emph>P2\<turnstile>Q\<^emph>R"
  by transfer (metis camera_comm camera_valid_op n_valid_ne)

lemma upred_sep_pure: "\<lbrakk>P\<turnstile>Q;P\<turnstile>\<upharpoonleft>b\<rbrakk> \<Longrightarrow> P\<turnstile>Q\<^emph>\<upharpoonleft>b"
  by transfer (meson n_incl_def n_incl_refl)

lemma upred_wand_holdsI: "Q \<turnstile> R \<Longrightarrow> upred_holds (Q-\<^emph>R)"
  by (metis upred_wandI upred_holds_entails upred_true_sep upred_sep_comm)
lemma upred_wand_holdsE: "upred_holds (Q-\<^emph>R) \<Longrightarrow> Q \<turnstile> R"
  by transfer (metis \<epsilon>_left_id camera_valid_op dual_order.refl)

lemma upred_own_core_persis: "Own(a) \<turnstile> \<box>Own(core a)"
  by (auto simp: upred_entails.rep_eq upred_own.rep_eq upred_persis.rep_eq camera_core_mono_n)

lemma upred_entails_wand_holdsL: "\<lbrakk>P \<turnstile> Q; upred_holds (Q-\<^emph>R)\<rbrakk> \<Longrightarrow> upred_holds (P-\<^emph>R)"
  by transfer (metis camera_comm camera_valid_op)

lemma upred_entails_wand_holdsR: "\<lbrakk>Q \<turnstile> R; upred_holds (P-\<^emph>Q)\<rbrakk> \<Longrightarrow> upred_holds (P-\<^emph>R)"
  by transfer auto

lemma upred_entails_wand_holdsR2: "\<lbrakk>Q \<turnstile> R; upred_holds (P1-\<^emph>P2-\<^emph>Q)\<rbrakk> \<Longrightarrow> upred_holds (P1-\<^emph>P2-\<^emph>R)"
  by transfer auto

lemma pure_entailsI: "(p \<Longrightarrow> q) \<Longrightarrow> \<upharpoonleft>p\<turnstile>\<upharpoonleft>q"
  by (auto simp: upred_pure_def upred_entails.rep_eq Abs_upred_f_inverse)

lemma discrete_valid: "\<V>(a::'a::dcamera) \<stileturn>\<turnstile> \<upharpoonleft>(valid a)"
  apply (rule upred_entail_eqI; auto simp: upred_valid.rep_eq upred_pure.rep_eq)
  using dcamera_valid_iff by blast+

lemma own_op: "Own(a\<cdot>b) \<stileturn>\<turnstile> Own(a) \<^emph> Own(b)"
  apply (rule upred_entail_eqI)
  unfolding upred_own.rep_eq upred_sep.rep_eq
  apply (rule iffI)
  apply (metis camera_assoc n_incl_def n_incl_op_extend n_incl_refl)
  apply (erule exE)+
  by (smt (z3) camera_assoc camera_comm n_incl_def ofe_trans op_equiv)

lemma own_valid2: "upred_holds (Own(a1) -\<^emph> Own (a2) -\<^emph> \<V>(a1\<cdot>a2))"
  apply (rule upred_wand_holdsI)
  apply (rule upred_wandI)
  using own_op own_valid upred_entails_trans upred_entail_eq_def by blast

lemma entails_pure_extend: "\<lbrakk>P\<turnstile>\<upharpoonleft>b;b \<Longrightarrow> P\<turnstile>Q\<rbrakk> \<Longrightarrow> P\<turnstile>Q"
  by transfer blast

lemma upred_wand_holds2I: "P\<^emph>Q\<turnstile>R \<Longrightarrow> upred_holds (P -\<^emph> Q -\<^emph> R)"
  apply (rule upred_wand_holdsI)
  apply (rule upred_wandI)
  by assumption
lemma upred_wand_holds2E: "upred_holds (P -\<^emph> Q -\<^emph> R) \<Longrightarrow> P\<^emph>Q\<turnstile>R"
  apply (rule upred_wandE)  
  apply (rule upred_wand_holdsE)
  by assumption

lemma upred_wand_mono: "\<lbrakk>P\<turnstile>P'; Q\<turnstile>Q'\<rbrakk> \<Longrightarrow> (P'-\<^emph>Q)\<turnstile>(P-\<^emph>Q')"
  by transfer (metis camera_comm camera_valid_op)

lemma upred_wand_disj: "\<lbrakk>(P-\<^emph>Q)\<turnstile>R; (P'-\<^emph>Q)\<turnstile>R\<rbrakk> \<Longrightarrow> ((P\<or>\<^sub>uP')-\<^emph>Q)\<turnstile>R"
  by transfer metis

lemma upred_wand_disj_apply: "\<lbrakk>P\<^emph>(Q-\<^emph>R)\<turnstile>S; P'\<^emph>(Q'-\<^emph>R)\<turnstile>S\<rbrakk> \<Longrightarrow> (P\<or>\<^sub>uP')\<^emph>((Q\<or>\<^sub>uQ')-\<^emph>R)\<turnstile>S"
  by transfer metis

lemma upred_own_nothing_true: "Own \<epsilon> \<stileturn>\<turnstile> upred_emp"
  by (rule upred_entail_eqI) (auto simp: upred_pure.rep_eq upred_own.rep_eq)

lemma upred_own_nothing_emp_eq: "Own \<epsilon> = upred_emp"
  by transfer simp  
  
lemma upred_persis_mono: "P \<turnstile> Q \<Longrightarrow> \<box> P \<turnstile> \<box> Q"
  by (auto simp: upred_entails.rep_eq upred_persis.rep_eq camera_core_n_valid)

lemma upred_persis_mono_frame: "P\<^emph>Q\<turnstile>R \<Longrightarrow> P\<^emph>\<box>Q\<turnstile>R"
  by transfer (metis camera_core_id n_incl_op_extend order_refl)  
  
lemma upred_persisE: "\<box> P \<turnstile> P"
  by (auto simp: upred_entails.rep_eq upred_persis.rep_eq)
    (metis camera_core_id n_incl_def nle_le ofe_refl upred_def_def upred_def_rep)

lemma upred_persis_conj_sep: "(\<box>P) \<and>\<^sub>u (\<box>Q) \<turnstile> (\<box>P) \<^emph> \<box>Q"
  by transfer (metis camera_core_id camera_core_idem ofe_refl)

lemma upred_persis_sep:"(\<box>P) \<^emph> (\<box>Q) \<turnstile> \<box>(P\<^emph>Q)"
  by transfer (metis camera_comm camera_core_id camera_core_idem camera_core_mono_n n_incl_def ofe_refl order_refl)  

lemma upred_persis_idem: "\<box>P \<turnstile> \<box>\<box>P"
  by transfer (metis camera_core_idem)
    
lemma upred_later_mono: "P\<turnstile>Q \<Longrightarrow> \<triangleright>P \<turnstile> \<triangleright>  Q"
  apply transfer
  using Rep_sprop diff_le_self by blast

lemma upred_later_mono_extR: "P\<^emph>R\<turnstile>Q \<Longrightarrow> P \<^emph> \<triangleright>R \<turnstile> \<triangleright>Q"
  by transfer 
  (meson diff_le_self n_incl_refl ne_sprop_weaken ofe_down_contr ofe_eq_limit valid_raw_non_expansive)

lemma upred_later_mono_extL: "P\<^emph>R\<turnstile>Q \<Longrightarrow> (\<triangleright>P) \<^emph> R \<turnstile> \<triangleright>Q"
  by transfer
  (meson diff_le_self n_incl_refl ne_sprop_weaken ofe_down_contr ofe_eq_limit valid_raw_non_expansive)

lemma upred_laterI: "P \<turnstile> \<triangleright>P" by transfer simp

lemma upred_later_sep: "\<triangleright>(P\<^emph>Q) \<stileturn>\<turnstile> (\<triangleright>P) \<^emph> \<triangleright>Q"
  apply (rule upred_entail_eqI) 
  apply transfer 
  apply auto
  apply (metis camera_core_id ofe_refl)
  apply (smt (verit, ccfv_threshold) Rep_sprop camera_extend diff_le_self mem_Collect_eq ofe_refl 
    ofe_sym order_refl upred_def_def upred_weaken)
  by (meson diff_le_self ofe_mono)

lemma upred_later_impl: "(\<triangleright> (P \<longrightarrow>\<^sub>u Q)) \<turnstile> ((\<triangleright>P) \<longrightarrow>\<^sub>u (\<triangleright>Q))"
  by transfer
    (smt (verit, ccfv_threshold) Rep_sprop diff_le_mono diff_le_self le_zero_eq mem_Collect_eq)

lemma upred_persis_later: "\<box>\<triangleright>P \<stileturn>\<turnstile> \<triangleright>\<box>P"
  by (rule upred_entail_eqI)
    (simp add: upred_later.rep_eq upred_persis.rep_eq)

lemma upred_later_disj: "\<triangleright>(P\<or>\<^sub>uQ) \<stileturn>\<turnstile> (\<triangleright>P) \<or>\<^sub>u (\<triangleright>Q)"
  apply (rule upred_entail_eqI)
  by transfer auto

lemma pull_exists_antecedent: "(\<exists>\<^sub>u x. (P x \<^emph> Q)) \<turnstile> R \<Longrightarrow> (\<exists>\<^sub>u x. P x) \<^emph> Q \<turnstile> R"
  by transfer' blast

lemma pull_exists_eq: "(\<exists>\<^sub>u x. P x) \<^emph> Q = (\<exists>\<^sub>u x. (P x \<^emph> Q))"
  by transfer blast

lemma pull_exists_antecedentR: "(\<exists>\<^sub>u x. (Q \<^emph> P x)) \<turnstile> R \<Longrightarrow> Q \<^emph> (\<exists>\<^sub>u x. P x) \<turnstile> R"
  by transfer' blast
  
lemma pull_exists_antecedent2: "(\<exists>\<^sub>u x. (P x \<^emph> Q \<^emph> Q')) \<turnstile> R \<Longrightarrow> (\<exists>\<^sub>u x. P x) \<^emph> Q \<^emph> Q' \<turnstile> R"
  by transfer' blast

lemma pull_forall_antecedent: "(\<forall>\<^sub>u x. (P x \<^emph> Q)) \<turnstile> R \<Longrightarrow> (\<forall>\<^sub>u x. P x) \<^emph> Q \<turnstile> R"
  by transfer' blast

lemma pull_forall_antecedent': "(\<forall>\<^sub>u x. (Q \<^emph> P x)) \<turnstile> R \<Longrightarrow> Q \<^emph> (\<forall>\<^sub>u x. P x) \<turnstile> R"
  by transfer' blast

lemma upred_existsE: "(\<forall>x. (P x \<turnstile> Q)) \<Longrightarrow> (\<exists>\<^sub>u x. P x) \<turnstile> Q"
  by transfer' blast

lemma upred_existsE': "(\<And>x. P x \<turnstile> Q) \<Longrightarrow> (\<exists>\<^sub>u x. P x) \<turnstile> Q"
  by (rule upred_existsE) simp

lemma upred_existsE_eq: "((\<exists>\<^sub>u x. P x) \<turnstile> Q) \<longleftrightarrow> (\<forall>x. P x \<turnstile> Q)"
  by transfer blast

lemma upred_existsI: "P \<turnstile> Q x \<Longrightarrow> P \<turnstile> (\<exists>\<^sub>u x. Q x)"
  by transfer blast

lemma pers_forall: "(\<forall>\<^sub>u x. \<box> (P x)) \<stileturn>\<turnstile> \<box> (\<forall>\<^sub>u x. P x)"
  apply (rule upred_entail_eqI) by transfer' simp

lemma upred_forallI: "(\<And>x. P \<turnstile> Q x) \<Longrightarrow> P \<turnstile> (\<forall>\<^sub>u x. Q x)"
  by transfer simp

lemma upred_forall_inst: "\<And>y. (\<forall>\<^sub>u x. P x) \<turnstile> P y"
  by transfer' blast
  
lemma upred_entails_substE: "\<lbrakk>P\<turnstile>Q; R \<^emph> Q \<turnstile> T\<rbrakk> \<Longrightarrow> R \<^emph> P \<turnstile> T"
  by transfer' (metis camera_comm camera_valid_op n_valid_ne)

lemma upred_entails_substE': "\<lbrakk>P\<turnstile>Q; R \<and>\<^sub>u Q \<turnstile> T\<rbrakk> \<Longrightarrow> R \<and>\<^sub>u P \<turnstile> T"
  by transfer blast
  
lemma upred_entails_substI: "\<lbrakk>P\<turnstile>Q; R\<turnstile>T\<^emph>P\<rbrakk> \<Longrightarrow> R\<turnstile>T\<^emph>Q"
  by transfer (metis camera_comm camera_valid_op n_valid_ne)

lemma upred_pure_impl: "(P \<Longrightarrow> Q \<turnstile> R) \<Longrightarrow> Q \<^emph> (\<upharpoonleft>P) \<turnstile> R"
  by (metis (full_types) entails_pure_extend upred_entails_eq upred_sep_comm upred_true_sep upred_wandE)

lemma upred_pure_impl': "(P \<Longrightarrow> Q \<turnstile> R) \<Longrightarrow> Q \<and>\<^sub>u (\<upharpoonleft>P) \<turnstile> R"
  by transfer simp

lemma upred_pure_sep_conj: "(\<upharpoonleft>b) \<^emph> P \<stileturn>\<turnstile> \<upharpoonleft>b \<and>\<^sub>u P"
  apply (rule upred_entail_eqI)
  by transfer (metis camera_comm n_incl_def n_incl_refl order_refl)

lemma upred_eqI: "\<upharpoonleft>(a=b) \<turnstile> a=\<^sub>ub"
  by transfer (simp add: ofe_refl)

lemma upred_eq_comm: "a=\<^sub>ub = b=\<^sub>ua"
  by transfer (simp add: ofe_sym)  
  
lemma upred_eqE: "P\<turnstile>Q \<Longrightarrow> R\<^emph>(P=\<^sub>uR)\<turnstile>Q"
  by (simp add: upred_entails.rep_eq upred_sep.rep_eq upred_eq.rep_eq)
    (metis le_refl n_equiv_upred_f.rep_eq n_incl_def upred_def_rep upred_equiv_upred_f)

lemma upred_frame: "P\<turnstile>Q \<Longrightarrow> P\<^emph>R\<turnstile>Q\<^emph>R"
  by (simp add: upred_sep_mono)

lemma upred_frameL: "R\<turnstile>Q \<Longrightarrow> P\<^emph>R\<turnstile>P\<^emph>Q"
    by (simp add: upred_sep_mono)

lemma false_sep [simp]: "(P \<^emph> \<upharpoonleft>False) = \<upharpoonleft>False"
  by transfer' blast
lemma false_entails [simp]: "\<upharpoonleft>False \<turnstile> P"
  by transfer' blast

lemma false_wand [simp]: "((\<upharpoonleft>False) -\<^emph> P) = upred_emp"
  by transfer simp

lemma pure_dupl: "(\<upharpoonleft>b) = (\<upharpoonleft>b) \<^emph> (\<upharpoonleft>b)"
  by transfer (meson n_incl_def n_incl_refl)

lemma own_unit: "\<Rrightarrow>\<^sub>b (Own \<epsilon>)"
  by transfer auto

lemma bupd_emp: "P=upred_emp \<Longrightarrow> \<Rrightarrow>\<^sub>b P = P"
  by transfer auto

lemma add_holds: "\<lbrakk>upred_holds P; Q\<^emph>P\<turnstile>R\<rbrakk> \<Longrightarrow> Q\<turnstile>R" 
  by transfer (metis \<epsilon>_left_id camera_comm camera_valid_op ofe_refl)

lemma own_updateP: "a \<leadsto>: P \<Longrightarrow> Own a ==\<^emph> (\<exists>\<^sub>u a'. \<upharpoonleft>(P a') \<^emph> Own a')"
  unfolding camera_updP_def
  by transfer (metis \<epsilon>_left_id camera_assoc n_incl_op_extend n_valid_incl_subst ofe_refl)

lemma upd_frameR: "P \<^emph> \<Rrightarrow>\<^sub>b Q \<turnstile> \<Rrightarrow>\<^sub>b (P \<^emph> Q)"
  by transfer
  (smt (z3) camera_assoc camera_comm n_valid_incl_subst ofe_refl ofe_sym order_refl total_n_inclI)

lemma upd_frameL: "(\<Rrightarrow>\<^sub>bP) \<^emph> Q \<turnstile> \<Rrightarrow>\<^sub>b (P \<^emph> Q)"
  by transfer
  (metis (mono_tags, opaque_lifting) camera_assoc n_valid_incl_subst ofe_refl ofe_sym order_refl total_n_inclI)

lemma upd_idem: "\<Rrightarrow>\<^sub>b \<Rrightarrow>\<^sub>b P \<turnstile> \<Rrightarrow>\<^sub>b P"
  by transfer blast

lemma upd_mono: "P\<turnstile>Q \<Longrightarrow> \<Rrightarrow>\<^sub>bP\<turnstile>\<Rrightarrow>\<^sub>bQ"
  by transfer (meson camera_valid_op)

lemma updI: "P \<turnstile> \<Rrightarrow>\<^sub>b P" by transfer auto
  
lemma upd_frame: "(\<Rrightarrow>\<^sub>bP) \<^emph> (\<Rrightarrow>\<^sub>bQ) \<turnstile> \<Rrightarrow>\<^sub>b(P\<^emph>Q)"
proof -
  have step1: "(\<Rrightarrow>\<^sub>bP) \<^emph> (\<Rrightarrow>\<^sub>bQ) \<turnstile> \<Rrightarrow>\<^sub>b (P \<^emph> (\<Rrightarrow>\<^sub>bQ))" using upd_frameL by blast
  have step2: "\<Rrightarrow>\<^sub>b (P \<^emph> (\<Rrightarrow>\<^sub>bQ)) \<turnstile> \<Rrightarrow>\<^sub>b \<Rrightarrow>\<^sub>b (P \<^emph> Q)" using upd_mono[OF upd_frameR] by auto
  from upred_entails_trans[OF step1 step2] have "(\<Rrightarrow>\<^sub>bP) \<^emph> (\<Rrightarrow>\<^sub>bQ) \<turnstile> \<Rrightarrow>\<^sub>b \<Rrightarrow>\<^sub>b (P \<^emph> Q)" .
  from upred_entails_trans[OF this upd_idem] show ?thesis .
qed

lemma upd_mono_ext: "R\<^emph>Q\<turnstile>P \<Longrightarrow> R\<^emph>\<Rrightarrow>\<^sub>bQ\<turnstile>\<Rrightarrow>\<^sub>bP"
  using upd_frameR upd_mono upred_entails_trans by blast

lemma own_alloc: "valid a \<Longrightarrow> \<Rrightarrow>\<^sub>b Own a"
  sorry (* Axiomatized as proof in Coq is not easily reproducible. *)

lemma own_update: "a\<leadsto>{b} \<Longrightarrow> Own a ==\<^emph> Own b"
  unfolding camera_upd_def
  by transfer (metis camera_assoc camera_comm camera_valid_op empty_iff insert_iff n_incl_refl n_valid_incl_subst)

lemma add_own: "\<lbrakk>valid a; Q\<^emph>(Own a)\<turnstile>\<Rrightarrow>\<^sub>bR\<rbrakk> \<Longrightarrow> Q\<turnstile>\<Rrightarrow>\<^sub>bR"
proof -
  assume assms: "valid a" "Q\<^emph>(Own a)\<turnstile>\<Rrightarrow>\<^sub>bR"
  from own_alloc[OF this(1)] have "\<Rrightarrow>\<^sub>b Own a" .
  from assms(2) have "Q\<^emph>\<Rrightarrow>\<^sub>b Own a\<turnstile>\<Rrightarrow>\<^sub>b R"
    by (meson upd_frameR upd_mono upd_idem upred_entails_trans)
    from add_holds[OF \<open>\<Rrightarrow>\<^sub>b Own a\<close> this] show ?thesis .
qed

lemma upred_pureI: "b \<Longrightarrow> (P \<turnstile> \<upharpoonleft>b)"
  by transfer blast

lemma upred_frame_empL: "upred_emp \<turnstile> Q \<Longrightarrow> R \<turnstile> Q\<^emph>R"
 by (metis upred_frameL upred_sep_comm upred_true_sep)

lemma upred_pers_impl_pure: "\<box>((\<upharpoonleft>P)\<longrightarrow>\<^sub>uQ) \<stileturn>\<turnstile> ((\<upharpoonleft>P) \<longrightarrow>\<^sub>u \<box>Q)"
  apply (rule upred_entail_eqI)
  apply transfer apply auto
  using camera_core_mono camera_core_n_valid apply blast
  by (metis \<epsilon>_right_id incl_def incl_n_incl order_refl)

lemma upred_implI: "P\<and>\<^sub>uQ\<turnstile>R \<Longrightarrow> P\<turnstile>(Q\<longrightarrow>\<^sub>uR)"
  by transfer (meson incl_n_incl)

lemma upred_implI': "P\<turnstile>(Q\<longrightarrow>\<^sub>uR) \<Longrightarrow> P\<and>\<^sub>uQ\<turnstile>R"
  by transfer (metis \<epsilon>_right_id incl_def order_refl)

lemma upred_implI_pure: "(P \<Longrightarrow> Q\<turnstile>R) \<Longrightarrow> Q\<turnstile>((\<upharpoonleft>P)\<longrightarrow>\<^sub>uR)"
  apply transfer using incl_n_incl by blast 

lemma upred_implE_pure: "\<lbrakk>P; R\<turnstile>Q\<rbrakk> \<Longrightarrow> ((\<upharpoonleft>P)\<longrightarrow>\<^sub>uR)\<turnstile>Q"
  by transfer (metis \<epsilon>_right_id incl_def order_refl)

lemma upred_emp_impl: "(upred_emp \<longrightarrow>\<^sub>u P) \<stileturn>\<turnstile> P"
  apply (rule upred_entail_eqI)  
  apply transfer apply auto
  apply (metis \<epsilon>_right_id incl_def order_refl)
  using incl_n_incl by blast

lemma upred_holds_persis: "upred_holds P \<Longrightarrow> upred_holds (\<box>P)"
  apply transfer using camera_core_n_valid by blast

lemma upred_holds_persis': "upred_holds P \<Longrightarrow> P \<turnstile> \<box>P"
apply transfer using camera_core_n_valid by blast

lemma entails_impl_true: "(P \<turnstile> Q) \<longleftrightarrow> (upred_emp \<turnstile> (P\<longrightarrow>\<^sub>uQ))"
  by transfer (metis camera_core_id camera_core_n_valid incl_def order_refl)

lemma upred_conj_dupl: "P \<stileturn>\<turnstile> P \<and>\<^sub>u P"
  apply (rule upred_entail_eqI)
  by transfer simp

lemma loeb_weak: "((\<triangleright>P) \<turnstile> (P::'a::ucamera upred_f)) \<Longrightarrow> (upred_emp \<turnstile> P)"
proof -
  assume assm: "(\<triangleright>P) \<turnstile> P"
  define floeb_pre where floeb: "floeb_pre \<equiv> \<lambda>P (Q::'a upred_f). ((\<triangleright>Q) \<longrightarrow>\<^sub>u P)"
  have "\<And>Q. contractive (floeb_pre Q)" apply (auto simp: contractive_def floeb) apply transfer
    apply auto
    apply (smt (verit, best) Rep_sprop Suc_less_eq Suc_pred Zero_not_Suc diff_Suc_Suc diff_self_eq_0 
      diff_zero le_antisym le_imp_less_Suc lessI less_Suc_eq_le less_nat_zero_code mem_Collect_eq 
      nat.inject nat_le_linear not0_implies_Suc not_gr_zero not_less_eq_eq order.trans order_refl zero_less_diff)
    by (smt (verit, best) Rep_sprop Suc_pred bot_nat_0.not_eq_extremum diff_is_0_eq lessI 
      less_or_eq_imp_le mem_Collect_eq order.trans zero_less_diff)
  then have floeb_contr: "\<And>Q. (floeb_pre Q) \<in> {f. contractive f}" by simp
  define Q where q: "Q = fixpoint (Abs_contr (floeb_pre P))"
  have q_eq: "Q \<stileturn>\<turnstile> ((\<triangleright>Q) \<longrightarrow>\<^sub>u P)" 
    apply (rule upred_entail_eqI)
    using fixpoint_unfold[of "(Abs_contr (floeb_pre P))", unfolded q[symmetric] 
      Abs_contr_inverse[OF floeb_contr] ofe_eq_upred_f.rep_eq, unfolded floeb]
    by blast
  have "\<triangleright>Q \<turnstile> P" 
    apply (rule upred_entails_trans[OF upred_entail_eqL[OF upred_conj_dupl]])
    apply (rule upred_entails_substE'[OF upred_laterI])
    apply (rule upred_entails_trans[OF _ assm])
    apply (rule upred_implI')
    apply (rule upred_entails_trans[OF _ upred_later_impl])
    apply (rule upred_later_mono)
    by (rule upred_entail_eqL[OF q_eq])
  show ?thesis 
    apply (rule upred_entails_trans[OF _ assm])
    apply (rule upred_entails_trans[OF _ upred_later_mono[OF \<open>\<triangleright>Q\<turnstile>P\<close>]])
    apply (rule upred_entails_trans[OF _ upred_laterI])+
    apply (rule upred_entails_trans[OF _ upred_entail_eqR[OF q_eq]])
    by (auto simp: entails_impl_true[symmetric] \<open>\<triangleright>Q\<turnstile>P\<close>)
qed

lemma loeb: "((\<triangleright>P) \<longrightarrow>\<^sub>u P ) \<turnstile> P"
  apply (subst entails_impl_true)
  apply (rule loeb_weak)
  apply (rule upred_implI)
  apply (rule upred_entails_substE'[OF upred_entail_eqL[OF upred_conj_dupl]])
  apply (subst upred_conj_assoc)
  apply (rule upred_entails_substE'[OF upred_laterI])
  apply (subst upred_conj_comm)
  apply (subst upred_conj_comm2R)
  apply (rule upred_entails_substE'[OF upred_later_impl])
  apply (rule upred_entails_substE'[OF upred_impl_apply, unfolded upred_conj_assoc])
  apply (subst upred_conj_comm)
  by (auto intro: upred_entails_trans[OF upred_impl_apply])

lemma loeb_persis: "\<box>((\<box>\<triangleright>P) \<longrightarrow>\<^sub>u P ) \<turnstile> P"
  apply (rule upred_entails_trans[OF _ upred_persisE])
  apply (rule upred_entails_trans[OF _ loeb])
  apply (rule upred_implI)
  apply (rule upred_entails_substE'[OF upred_entail_eqR[OF upred_persis_later]])
  apply (rule upred_entails_trans[OF upred_persis_conj_sep])
  apply (rule upred_entails_substE[OF upred_persis_idem])
  apply (subst upred_sep_comm)
  apply (rule upred_entails_trans[OF upred_persis_sep])
  by (auto intro!: upred_entails_trans[OF upred_persis_mono[OF upred_entails_conj_sep]] 
    upred_entails_trans[OF upred_persis_mono[OF upred_impl_apply]] )

lemma upred_persisIR:"\<box>P \<turnstile> Q \<Longrightarrow> \<box>P \<turnstile> \<box>Q"
  by (simp add: camera_core_idem camera_core_n_valid upred_entails.rep_eq upred_persis.rep_eq)

lemma upred_holds_subst: "\<lbrakk>P\<turnstile>Q; upred_holds P\<rbrakk> \<Longrightarrow> upred_holds Q"
  by transfer simp

lemma upred_holds_forall: "(\<And>x. upred_holds (P x)) \<Longrightarrow> upred_holds (\<forall>\<^sub>u x. P x)"
  by transfer' auto

definition can_be_split :: "('a::ucamera) upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" where
  "can_be_split PQ P Q \<equiv> PQ \<stileturn>\<turnstile> P \<^emph> Q"

lemma can_be_split_refl: "can_be_split (P\<^emph>Q) P Q"
  unfolding can_be_split_def by (simp add: upred_entails_eq_eq)

lemma can_be_split_rev: "can_be_split P Q R \<Longrightarrow> can_be_split P R Q"
  unfolding can_be_split_def upred_entail_eq_def by (simp add: upred_sep_comm)

lemma can_be_split_mono: "\<lbrakk>can_be_split P P1 P2; can_be_split Q Q1 Q2\<rbrakk> \<Longrightarrow> can_be_split (P\<^emph>Q) (P1\<^emph>Q1) (P2\<^emph>Q2)"
  by (smt (verit, del_insts) can_be_split_def upred_entail_eq_def upred_sep_assoc_eq 
    upred_sep_comm2_eq upred_sep_mono) 

lemma can_be_splitI: "P \<stileturn>\<turnstile> Q \<^emph> R \<Longrightarrow> can_be_split P Q R" unfolding can_be_split_def .
  
lemma can_be_split_R_R: "can_be_split P P1 P2 \<Longrightarrow> can_be_split (Q\<^emph>P) P1 (Q\<^emph>P2)"
  by (metis can_be_split_mono can_be_split_refl upred_sep_comm upred_true_sep)

lemma can_be_split_sepL: "can_be_split P Q R \<Longrightarrow> can_be_split (P\<^emph>S) (Q\<^emph>S) R"
  by (simp add: can_be_split_def upred_entail_eq_def upred_frame upred_sep_comm2_eq)

lemma can_be_split_sepR: "can_be_split P Q R \<Longrightarrow> can_be_split (P\<^emph>S) Q (R\<^emph>S)"
  by (simp add: can_be_split_def upred_entail_eq_def upred_frame upred_sep_assoc_eq)
  
lemma split_trans: "\<lbrakk>can_be_split P P1 P2; P1 \<turnstile> Q; Q\<^emph>P2 \<turnstile> R\<rbrakk> \<Longrightarrow> P \<turnstile> R"
  unfolding can_be_split_def by (meson upred_entail_eqL upred_entails_trans upred_frame)

lemma split_frame: "\<lbrakk>can_be_split P P1 P2; can_be_split Q Q1 Q2; P1\<turnstile>Q1; P2\<turnstile>Q2\<rbrakk> \<Longrightarrow> P\<turnstile>Q"
  by (meson can_be_split_def split_trans upred_entail_eqR upred_entails_refl upred_entails_trans upred_sep_mono)

subsubsection \<open> Persistent predicates \<close>
definition persistent :: "('a::ucamera) upred_f \<Rightarrow> bool" where "persistent P \<equiv> P \<turnstile> \<box>P"
lemma persistentI: "persistent P \<Longrightarrow> P \<turnstile> \<box>P"
  unfolding persistent_def .

lemma persistent_holds_sep: 
  "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> upred_holds (P\<^emph>Q) \<longleftrightarrow> upred_holds P \<and> upred_holds Q"
  unfolding persistent_def upred_holds.rep_eq upred_entails.rep_eq upred_persis.rep_eq upred_sep.rep_eq
  by (smt (verit, ccfv_threshold) camera_comm camera_core_id le_cases3 n_incl_def ofe_refl upred_def_def upred_def_rep)

lemma persistent_holds_sep': 
  "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> (P\<^emph>Q) \<stileturn>\<turnstile> P \<and>\<^sub>u Q"
  by (rule upred_entail_eqI) (metis (no_types, lifting) camera_core_id ofe_refl persistent_def 
    upred_conj.rep_eq upred_entailsE upred_entails_conj_sep upred_persis.rep_eq upred_sep.rep_eq)
  
named_theorems pers_rule
method pers_solver = (rule pers_rule)+

lemma persistent_persis [pers_rule]: "persistent (\<box>P)"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq camera_core_idem)

lemma persistent_pure [pers_rule]: "persistent (\<upharpoonleft>P)"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_pure.rep_eq)  

lemma persistent_valid [pers_rule]: "persistent (\<V>(a))"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_valid.rep_eq)
  
lemma persistent_core_own [pers_rule]: "persistent (Own(a::'a::{core_id,ucamera}))"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_own.rep_eq core_id)

lemma persistent_core_own2 [pers_rule]: "pcore_id_pred (a::'a::ucamera) \<Longrightarrow> persistent (Own a)"
  unfolding persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_own.rep_eq core_id_pred
  using camera_core_mono_n by fastforce

lemma persistent_eq [pers_rule]: "persistent (a=\<^sub>ub)"
  unfolding persistent_def by transfer simp

lemma persistent_later [pers_rule]: "persistent P \<Longrightarrow> persistent (\<triangleright> P)"
  unfolding persistent_def
  by (rule upred_entails_trans[OF upred_later_mono[of P "\<box>P"] upred_entail_eqR[OF upred_persis_later]])

lemma persistent_conj [pers_rule]: "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P \<and>\<^sub>u Q)"
  by (auto simp: persistent_def upred_conj.rep_eq upred_entails.rep_eq upred_persis.rep_eq)

lemma persistent_disj [pers_rule]: "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P \<or>\<^sub>u Q)"
  by (auto simp: persistent_def upred_disj.rep_eq upred_entails.rep_eq upred_persis.rep_eq)
  
lemma persistent_exists [pers_rule]: "(\<And>x. persistent (P x)) \<Longrightarrow> persistent (\<exists>\<^sub>u x. P x)"
  by (auto simp: upred_exists.rep_eq persistent_def upred_persis.rep_eq upred_entails.rep_eq)

lemma persistent_forall [pers_rule]: "(\<And>x. persistent (P x)) \<Longrightarrow> persistent (\<forall>\<^sub>u x. P x)"
  by (auto simp: upred_forall.rep_eq persistent_def upred_persis.rep_eq upred_entails.rep_eq)

lemma persistent_sep [pers_rule]: "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P \<^emph> Q)"
by (simp add: persistent_def upred_sep.rep_eq upred_entails.rep_eq upred_persis.rep_eq)
  (metis camera_comm camera_core_id camera_valid_op dual_order.refl n_incl_def ofe_refl 
    upred_def_def upred_def_rep)
  
lemma persistent_dupl: "persistent P \<Longrightarrow> P\<^emph>P \<stileturn>\<turnstile> P"
  unfolding persistent_def upred_entail_eq_def 
  by transfer (metis camera_core_id n_incl_def ofe_refl order_refl)

lemma persistent_dupl': "persistent P \<Longrightarrow> can_be_split P P P"
  unfolding can_be_split_def using persistent_dupl upred_entail_eq_symm by blast

lemma persistent_dupl_split: "persistent P \<Longrightarrow> can_be_split (Q\<^emph>P) (Q\<^emph>P) P"
  unfolding can_be_split_def using persistent_dupl upred_entail_eq_def upred_entails_substE 
  upred_sep_assoc upred_weakeningL by blast
  
lemma "persistent P \<Longrightarrow> ofe_eq P (P \<^emph> P)"
  unfolding persistent_def apply transfer
  by (metis camera_core_id n_incl_def ofe_refl order_refl)

lemma persistent_split: "\<lbrakk>persistent Q; Q\<^emph>R1\<turnstile>R2; P\<^emph>Q\<turnstile>T\<rbrakk> \<Longrightarrow> P\<^emph>Q\<^emph>R1\<turnstile>T\<^emph>R2"
proof -
  assume assms: "persistent Q" "Q\<^emph>R1 \<turnstile> R2" "P\<^emph>Q\<turnstile>T"
  from upred_sep_mono[OF this(3,2)] have "P\<^emph>Q\<^emph>Q\<^emph>R1 \<turnstile> T\<^emph>R2"
    using upred_entails_trans upred_sep_assoc_rev by blast
  moreover from persistent_dupl[OF assms(1)] have "P\<^emph>Q\<^emph>R1 \<turnstile> P\<^emph>Q\<^emph>Q\<^emph>R1"
    using upred_entail_eqR upred_entails_substE upred_frame upred_sep_assoc by blast
  ultimately show ?thesis using upred_entails_trans by blast
qed  

lemma persistent_trans: "\<lbrakk>persistent P; Q\<^emph>P\<turnstile>R \<Longrightarrow> R\<turnstile>T \<Longrightarrow> Q\<^emph>P\<turnstile>T\<rbrakk> \<Longrightarrow> (Q\<^emph>P\<turnstile>R \<Longrightarrow> R\<^emph>P\<turnstile>T \<Longrightarrow> Q\<^emph>P\<turnstile>T)"
  by (metis persistent_dupl upred_entail_eqR upred_entails_substE upred_sep_assoc_eq upred_sep_comm)

lemma persistent_keep: "\<lbrakk>persistent Q; P\<turnstile>Q\<rbrakk> \<Longrightarrow> P\<turnstile>P\<^emph>Q"
  unfolding persistent_def by transfer (metis camera_comm camera_core_id ofe_refl)

lemma persistent_persisI: "\<lbrakk>persistent P; P\<turnstile>Q\<rbrakk> \<Longrightarrow> P \<turnstile>\<box>Q"
  using persistent_def upred_entails_trans upred_persis_mono by blast

lemma upred_persis_frame: "\<lbrakk>persistent P; P\<^emph>Q\<turnstile>R\<rbrakk> \<Longrightarrow> P\<^emph>\<box>Q\<turnstile>\<box>R"
  by (meson persistent_persis persistent_persisI persistent_sep upred_entails_substE upred_persisE)

lemma persistent_sep_conj: "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> P \<and>\<^sub>u Q \<turnstile> P \<^emph> Q"
  unfolding persistent_def by transfer (metis camera_core_id ofe_refl)

lemma persistent_loebI: "\<lbrakk>persistent P; P\<^emph>(\<box>\<triangleright>Q)\<turnstile>Q\<rbrakk> \<Longrightarrow> P\<turnstile>Q"
  apply (rule upred_entails_trans[OF _ loeb_persis])
  apply (rule upred_entails_trans[OF persistentI])
  by (auto intro!: upred_persis_mono upred_entails_trans[OF upred_entails_refl upred_implI] 
    upred_entails_trans[OF persistent_sep_conj], pers_solver)

lemma loebI: "\<box>\<triangleright>Q\<turnstile>Q \<Longrightarrow> upred_holds Q"
  apply (subst upred_holds_entails)
  apply (rule persistent_loebI, pers_solver)
  apply (subst upred_sep_comm)
  by (auto simp: upred_true_sep)
  
subsubsection \<open> Timeless predicates \<close>
definition except_zero :: "'a::ucamera upred_f \<Rightarrow> 'a upred_f" ("\<diamondop>_") where 
  "except_zero P \<equiv> P \<or>\<^sub>u \<triangleright>\<upharpoonleft>False"

lemma except_zeroI: "P \<turnstile> \<diamondop> P"
  unfolding except_zero_def by transfer blast

lemma except_zero_sep: "\<diamondop>(P \<^emph> Q) \<stileturn>\<turnstile> (\<diamondop>P) \<^emph> (\<diamondop>Q)"
  apply (auto simp: except_zero_def intro!: upred_entail_eqI; transfer)
  using n_incl_def n_incl_refl by blast+

lemma except_zero_sepR: "(\<diamondop>P) \<^emph> Q \<turnstile> \<diamondop>(P \<^emph> Q)"
  by (auto intro: upred_entails_substE[OF except_zeroI] upred_entail_eqR[OF except_zero_sep])

lemma except_zero_sepL: "P \<^emph> (\<diamondop>Q) \<turnstile> \<diamondop>(P \<^emph> Q)"
  by (metis except_zero_sepR upred_sep_comm)
  
lemma persistent_except_zero [pers_rule]: "persistent P \<Longrightarrow> persistent (\<diamondop>P)"
  unfolding except_zero_def
  apply (pers_solver, assumption)
  by pers_solver

lemma except_zero_mono: "P\<turnstile>Q \<Longrightarrow> \<diamondop>P\<turnstile>\<diamondop>Q"
  unfolding except_zero_def by transfer  blast

lemma except_zero_idem: "\<diamondop>\<diamondop>P \<turnstile> \<diamondop>P"
  unfolding except_zero_def by transfer simp

lemma except_zero_mono_ext: "P\<^emph>Q\<turnstile>R \<Longrightarrow> P\<^emph>\<diamondop>Q\<turnstile>\<diamondop>R"
  using except_zero_mono except_zero_sepL upred_entails_trans by blast

lemma except_zero_bupd: "\<diamondop>\<Rrightarrow>\<^sub>bP\<turnstile>\<Rrightarrow>\<^sub>b\<diamondop>P"
  unfolding except_zero_def by transfer blast

definition is_except_zero :: "'a::ucamera upred_f \<Rightarrow> bool" where "is_except_zero P \<equiv> \<diamondop>P \<turnstile> P"

lemma is_except_zero_except_zero: "is_except_zero (\<diamondop>P)"
  unfolding is_except_zero_def by (rule except_zero_idem)

lemma is_except_zero_later: "is_except_zero (\<triangleright>P)"
  unfolding is_except_zero_def except_zero_def by transfer blast

definition timeless :: "'a::ucamera upred_f \<Rightarrow> bool" where "timeless P \<equiv> (\<triangleright>P) \<turnstile> \<diamondop>P"

named_theorems timeless_rule
method timeless_solver = (rule timeless_rule)+

lemma own_timeless [timeless_rule]: "timeless (Own (x::'a::ducamera))"
  by (auto simp: upred_own.rep_eq upred_entails.rep_eq upred_later.rep_eq except_zero_def 
    upred_disj.rep_eq upred_pure.rep_eq n_incl_def d_equiv timeless_def)

lemma timeless_pure [timeless_rule]: "timeless (\<upharpoonleft>(b))"
  unfolding timeless_def except_zero_def by transfer simp

lemma timeless_conj [timeless_rule]: "\<lbrakk>timeless P; timeless Q\<rbrakk> \<Longrightarrow> timeless (P\<and>\<^sub>uQ)"
  unfolding timeless_def except_zero_def by transfer blast

lemma timeless_disj [timeless_rule]: "\<lbrakk>timeless P; timeless Q\<rbrakk> \<Longrightarrow> timeless (P\<or>\<^sub>uQ)"
  unfolding timeless_def except_zero_def by transfer blast

lemma timeless_impl [timeless_rule]: "timeless Q \<Longrightarrow> timeless (P\<longrightarrow>\<^sub>uQ)"
  unfolding timeless_def except_zero_def apply transfer
  by (metis (mono_tags, lifting) Rep_sprop diff_le_mono diff_le_self diff_self_eq_0 mem_Collect_eq n_incl_refl)

lemma timeless_sep [timeless_rule]: "\<lbrakk>timeless P; timeless Q\<rbrakk> \<Longrightarrow> timeless (P\<^emph>Q)"
  unfolding timeless_def 
  apply (rule upred_entails_trans[OF upred_entail_eqL[OF upred_later_sep]])
  apply (rule upred_entails_trans[OF _ upred_entail_eqR[OF except_zero_sep]])
  by (auto intro: upred_sep_mono)

lemma timeless_wand [timeless_rule]: "timeless Q \<Longrightarrow> timeless (P-\<^emph>Q)"
  unfolding timeless_def except_zero_def apply transfer
  by (smt (verit, ccfv_threshold) Rep_sprop diff_diff_cancel diff_is_0_eq diff_right_commute mem_Collect_eq n_incl_refl nat_le_linear)

lemma timeless_forall [timeless_rule]: "(\<And>x. timeless (P x)) \<Longrightarrow> timeless (\<forall>\<^sub>u x. P x)"
  unfolding timeless_def except_zero_def by transfer' blast

lemma timeless_exists [timeless_rule]: "(\<And>x. timeless (P x)) \<Longrightarrow> timeless (\<exists>\<^sub>u x. P x)"
  unfolding timeless_def except_zero_def by transfer' blast

lemma timeless_persis [timeless_rule]: "timeless P \<Longrightarrow> timeless (\<box>P)"
  unfolding timeless_def except_zero_def apply transfer using camera_core_n_valid by blast

definition elim_modal :: "'a::ucamera upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" 
  where "elim_modal P P' Q Q' \<equiv> P \<^emph> (P'-\<^emph>Q') \<turnstile> Q"
  
lemma elim_modal_timeless: "\<lbrakk>P \<turnstile> \<diamondop>P'; is_except_zero Q\<rbrakk> \<Longrightarrow> elim_modal P P' Q Q"
  unfolding is_except_zero_def elim_modal_def
  by (metis except_zero_mono_ext upred_entails_refl upred_entails_trans upred_frame upred_sep_comm upred_wandE)

lemma elim_modal_entails: "\<lbrakk>elim_modal P P' Q Q'; P' \<turnstile> Q'\<rbrakk> \<Longrightarrow> P \<turnstile> Q"
proof -
  assume assms: "elim_modal P P' Q Q'" "P' \<turnstile> Q'"
  from upred_wand_holdsI[OF assms(2)] have "P' -\<^emph> Q'" .
  show ?thesis apply (rule add_holds[OF \<open>P'-\<^emph>Q'\<close>])
  by (rule assms(1)[unfolded elim_modal_def])
qed

lemma elim_modal_entails': "\<lbrakk>elim_modal P P' Q Q'; R \<^emph> P' \<turnstile> Q'\<rbrakk> \<Longrightarrow> R \<^emph> P \<turnstile> Q"
  by (metis elim_modal_def upred_entails_substE upred_sep_comm upred_wandI)

subsubsection \<open>Plain predicates\<close>
definition plain :: "'a::ucamera upred_f \<Rightarrow> bool" where "plain P \<equiv> P\<turnstile>\<^item>P"

named_theorems plain_rule
method plain_solver = (rule plain_rule)+

lemma plain_persistent: "plain P \<Longrightarrow> persistent P" 
  unfolding plain_def persistent_def apply transfer using n_incl_\<epsilon> by blast

lemma bupd_plain_sound: "\<lbrakk>plain P; \<Rrightarrow>\<^sub>b P\<rbrakk> \<Longrightarrow> P"
  unfolding plain_def by transfer (metis \<epsilon>_right_id n_incl_\<epsilon> verit_comp_simplify1(2))

lemma bupd_plain: "plain P \<Longrightarrow> \<Rrightarrow>\<^sub>b P \<turnstile> P"
  unfolding plain_def by transfer (metis \<epsilon>_right_id n_incl_\<epsilon> order_refl)

lemma plain_pure [plain_rule]: "plain (\<upharpoonleft>P)" unfolding plain_def by transfer blast
lemma plain_conj [plain_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<and>\<^sub>uQ)" unfolding plain_def by transfer fast
lemma plain_disj [plain_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<or>\<^sub>uQ)" unfolding plain_def by transfer fast
lemma plain_forall [plain_rule]: "(\<And>x. plain (P x)) \<Longrightarrow> plain (\<forall>\<^sub>u x. P x)" 
  unfolding plain_def by transfer blast
lemma plain_exists [plain_rule]: "(\<And>x. plain (P x)) \<Longrightarrow> plain (\<exists>\<^sub>u x. P x)" 
  unfolding plain_def by transfer blast
lemma plain_impl [plain_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<longrightarrow>\<^sub>uQ)" 
  unfolding plain_def apply transfer
  by (smt (verit, ccfv_threshold) Rep_sprop \<epsilon>_right_id incl_def mem_Collect_eq n_incl_\<epsilon> order_refl)
lemma plain_wand [plain_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P-\<^emph>Q)"
  unfolding plain_def apply transfer
  by (metis (mono_tags, lifting) Rep_sprop \<epsilon>_left_id \<epsilon>_right_id mem_Collect_eq n_incl_op_extend order_refl)
lemma plain_sep [plain_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<^emph>Q)" 
  unfolding plain_def apply transfer
  by (metis \<epsilon>_left_id camera_comm n_incl_def ofe_refl order_refl)  
lemma plain_plainly [plain_rule]: "plain (\<^item>P)" unfolding plain_def by transfer fast
lemma plain_eq [plain_rule]: "plain (a=\<^sub>ub)" unfolding plain_def by transfer blast
lemma plain_later [plain_rule]: "plain P \<Longrightarrow> plain (\<triangleright>P)" 
  unfolding plain_def apply transfer using Rep_sprop diff_le_self by blast
lemma plain_except_zero [plain_rule]: "plain P \<Longrightarrow> plain (\<diamondop>P)" unfolding except_zero_def
  by (plain_solver, assumption)+  plain_solver

method pers_solver' = (pers_solver; rule plain_persistent; plain_solver)

lemma persistent_impl: "\<lbrakk>plain P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P -\<^emph> Q)"
  unfolding plain_def persistent_def apply transfer
  by (metis (no_types, lifting) \<epsilon>_right_id camera_comm n_incl_op_extend ne_sprop_weaken ofe_eq_limit 
    order_eq_refl valid_raw_non_expansive)
end