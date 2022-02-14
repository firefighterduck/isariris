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

lemma upred_weakeningR2: "P\<^emph>Q\<^emph>R\<turnstile>Q\<^emph>R"
  by transfer (metis camera_comm le_refl n_incl_def)

lemma upred_entails_add: "\<lbrakk>P\<turnstile>Q; P\<and>\<^sub>uQ\<turnstile>R\<rbrakk> \<Longrightarrow> P\<turnstile>R"
  by transfer blast  

lemma upred_entails_conjI: "\<lbrakk>P\<turnstile>Q; P\<turnstile>R\<rbrakk> \<Longrightarrow> P \<turnstile> Q \<and>\<^sub>u R"
  by transfer blast
lemma upred_entails_conj_sep: "P \<^emph> Q \<turnstile> P \<and>\<^sub>u Q"
  by transfer (metis camera_comm le_refl n_incl_def)

lemma upred_disjE: "\<lbrakk>P\<turnstile>R; Q\<turnstile>R\<rbrakk> \<Longrightarrow> P\<or>\<^sub>uQ\<turnstile>R"
  by transfer' blast
lemma upred_disjE': "\<lbrakk>P\<^emph>Q\<turnstile>T; P\<^emph>R\<turnstile>T\<rbrakk> \<Longrightarrow> P\<^emph>(Q\<or>\<^sub>uR)\<turnstile>T"
  by transfer' blast
lemma upred_disjIL: "P\<turnstile>Q \<Longrightarrow> P\<turnstile>Q\<or>\<^sub>uR"
  by transfer blast
lemma upred_disjIR: "P\<turnstile>R \<Longrightarrow> P\<turnstile>Q\<or>\<^sub>uR"
  by transfer blast
  
lemma upred_entails_refl [simp]: "P\<turnstile>P" by (auto simp: upred_entails_def)

lemma upred_entails_eq: "P=Q \<Longrightarrow> P\<turnstile>Q" by simp
lemma upred_entails_eq_eq: "P=Q \<Longrightarrow> P\<stileturn>\<turnstile>Q" using upred_entails_eq upred_entail_eq_def by blast

lemma own_valid: "Own(a) \<turnstile> \<V>(a)"
  unfolding upred_entails.rep_eq upred_own.rep_eq upred_valid.rep_eq n_incl_def
  using camera_valid_op n_valid_ne by blast

lemma upred_holds_entails: "upred_holds P \<longleftrightarrow> ((\<upharpoonleft>True) \<turnstile> P)"
  by (auto simp: upred_holds.rep_eq upred_entails.rep_eq upred_pure.rep_eq)

lemma upred_entailsE: "P \<turnstile> Q \<Longrightarrow> (\<And>a n. \<lbrakk>n_valid a n; Rep_upred_f P a n\<rbrakk> \<Longrightarrow> Rep_upred_f Q a n)"
  by (auto simp: upred_entails.rep_eq)

lemma upred_entailsI: "(\<And>a n. \<lbrakk>n_valid a n; Rep_upred_f P a n\<rbrakk> \<Longrightarrow> Rep_upred_f Q a n) \<Longrightarrow> P \<turnstile> Q"
  by (auto simp: upred_entails.rep_eq)
  
lemma upred_wandI: "(P \<^emph> Q) \<turnstile> R \<Longrightarrow> P \<turnstile> (Q-\<^emph>R)"
  unfolding upred_entails.rep_eq upred_sep.rep_eq upred_wand.rep_eq
  using ofe_refl upred_def_rep upred_weaken_simple by blast
lemma upred_wandE: "P \<turnstile> (Q-\<^emph>R) \<Longrightarrow> (P \<^emph> Q) \<turnstile> R"
  by transfer (meson camera_valid_op dual_order.refl n_valid_ne ofe_sym total_n_inclI)

lemma upred_true_sep: "(P \<^emph> \<upharpoonleft>True) = P"
  apply transfer using n_incl_def by fastforce

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

lemma upred_own_nothing_true: "Own \<epsilon> \<stileturn>\<turnstile> \<upharpoonleft>True"
  by (rule upred_entail_eqI) (auto simp: upred_pure.rep_eq upred_own.rep_eq)

lemma upred_own_nothing_emp_eq: "Own \<epsilon> = upred_emp"
  by transfer simp  
  
lemma upred_persis_mono: "P \<turnstile> Q \<Longrightarrow> \<box> P \<turnstile> \<box> Q"
  by (auto simp: upred_entails.rep_eq upred_persis.rep_eq camera_core_n_valid)

lemma upred_persisE: "\<box> P \<turnstile> P"
  by (auto simp: upred_entails.rep_eq upred_persis.rep_eq)
    (metis camera_core_id n_incl_def nle_le ofe_refl upred_def_def upred_def_rep)

lemma upred_later_mono: "P\<turnstile>Q \<Longrightarrow> \<triangleright>P \<turnstile> \<triangleright> Q"
  apply transfer
  using Rep_sprop diff_le_self by blast

lemma upred_later_sep: "\<triangleright>(P\<^emph>Q) \<stileturn>\<turnstile> (\<triangleright>P) \<^emph> \<triangleright>Q"
  apply (rule upred_entail_eqI) 
  apply transfer 
  apply auto
  apply (metis camera_core_id ofe_refl)
  apply (smt (verit, ccfv_threshold) Rep_sprop camera_extend diff_le_self mem_Collect_eq ofe_refl 
    ofe_sym order_refl upred_def_def upred_weaken)
  by (meson diff_le_self ofe_mono)

lemma upred_persis_later: "\<box>\<triangleright>P \<stileturn>\<turnstile> \<triangleright>\<box>P"
  by (rule upred_entail_eqI)
    (simp add: upred_later.rep_eq upred_persis.rep_eq)

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
  
lemma "(\<exists>\<^sub>u x. P x) \<turnstile> Q \<Longrightarrow> P x \<turnstile> Q"
  by transfer' blast

lemma upred_existsE: "(\<forall>x. (P x \<turnstile> Q)) \<Longrightarrow> (\<exists>\<^sub>u x. P x) \<turnstile> Q"
  by transfer' blast

lemma upred_existsE': "(\<And>x. P x \<turnstile> Q) \<Longrightarrow> (\<exists>\<^sub>u x. P x) \<turnstile> Q"
  by (rule upred_existsE) simp

lemma upred_existsE_eq: "((\<exists>\<^sub>u x. P x) \<turnstile> Q) \<longleftrightarrow> (\<forall>x. P x \<turnstile> Q)"
  by transfer blast

lemma upred_existsI: "P \<turnstile> Q x \<Longrightarrow> P \<turnstile> (\<exists>\<^sub>u x. Q x)"
  by transfer blast

lemma upred_entails_exchange: "\<lbrakk>P\<turnstile>Q; R \<^emph> Q \<turnstile> T\<rbrakk> \<Longrightarrow> R \<^emph> P \<turnstile> T"
  by transfer' (metis camera_comm camera_valid_op n_valid_ne)
  
lemma upred_pure_impl: "(P \<Longrightarrow> Q \<turnstile> R) \<Longrightarrow> Q \<^emph> (\<upharpoonleft>P) \<turnstile> R"
  by (metis (full_types) entails_pure_extend upred_entails_eq upred_sep_comm upred_true_sep upred_wandE)

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

lemma upd_trans: "\<Rrightarrow>\<^sub>b \<Rrightarrow>\<^sub>b P \<turnstile> \<Rrightarrow>\<^sub>b P"
  by transfer blast

lemma upd_mono: "P\<turnstile>Q \<Longrightarrow> \<Rrightarrow>\<^sub>bP\<turnstile>\<Rrightarrow>\<^sub>bQ"
  by transfer (meson camera_valid_op)

lemma updI: "P \<turnstile> \<Rrightarrow>\<^sub>b P" by transfer auto
  
lemma upd_frame: "(\<Rrightarrow>\<^sub>bP) \<^emph> (\<Rrightarrow>\<^sub>bQ) \<turnstile> \<Rrightarrow>\<^sub>b(P\<^emph>Q)"
proof -
  have step1: "(\<Rrightarrow>\<^sub>bP) \<^emph> (\<Rrightarrow>\<^sub>bQ) \<turnstile> \<Rrightarrow>\<^sub>b (P \<^emph> (\<Rrightarrow>\<^sub>bQ))" using upd_frameL by blast
  have step2: "\<Rrightarrow>\<^sub>b (P \<^emph> (\<Rrightarrow>\<^sub>bQ)) \<turnstile> \<Rrightarrow>\<^sub>b \<Rrightarrow>\<^sub>b (P \<^emph> Q)" using upd_mono[OF upd_frameR] by auto
  from upred_entails_trans[OF step1 step2] have "(\<Rrightarrow>\<^sub>bP) \<^emph> (\<Rrightarrow>\<^sub>bQ) \<turnstile> \<Rrightarrow>\<^sub>b \<Rrightarrow>\<^sub>b (P \<^emph> Q)" .
  from upred_entails_trans[OF this upd_trans] show ?thesis .
qed

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
    by (meson upd_frameR upd_mono upd_trans upred_entails_trans)
    from add_holds[OF \<open>\<Rrightarrow>\<^sub>b Own a\<close> this] show ?thesis .
qed

lemma upred_pureI: "b \<Longrightarrow> (P \<turnstile> \<upharpoonleft>b)"
  by transfer blast

lemma upred_frame_empL: "upred_emp \<turnstile> Q \<Longrightarrow> R \<turnstile> Q\<^emph>R"
 by (metis upred_frameL upred_sep_comm upred_true_sep)

subsubsection \<open> Persistent predicates \<close>
definition persistent :: "('a::ucamera) upred_f \<Rightarrow> bool" where "persistent P \<equiv> P \<turnstile> \<box>P"

lemma persistent_holds_sep: 
  "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> upred_holds (P\<^emph>Q) \<longleftrightarrow> upred_holds P \<and> upred_holds Q"
  unfolding persistent_def upred_holds.rep_eq upred_entails.rep_eq upred_persis.rep_eq upred_sep.rep_eq
  by (smt (verit, ccfv_threshold) camera_comm camera_core_id le_cases3 n_incl_def ofe_refl upred_def_def upred_def_rep)

lemma persistent_holds_sep': 
  "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> (P\<^emph>Q) \<stileturn>\<turnstile> P \<and>\<^sub>u Q"
  by (rule upred_entail_eqI) (metis (no_types, lifting) camera_core_id ofe_refl persistent_def 
    upred_conj.rep_eq upred_entailsE upred_entails_conj_sep upred_persis.rep_eq upred_sep.rep_eq)
  
named_theorems pers_rule
  
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

lemma persistent_sep [pers_rule]: "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P \<^emph> Q)"
by (simp add: persistent_def upred_sep.rep_eq upred_entails.rep_eq upred_persis.rep_eq)
  (metis camera_comm camera_core_id camera_valid_op dual_order.refl n_incl_def ofe_refl 
    upred_def_def upred_def_rep)
  
lemma persistent_dupl: "persistent P \<Longrightarrow> P\<^emph>P \<stileturn>\<turnstile> P"
  unfolding persistent_def upred_entail_eq_def 
  by transfer (metis camera_core_id n_incl_def ofe_refl order_refl)

lemma "persistent P \<Longrightarrow> ofe_eq P (P \<^emph> P)"
  unfolding persistent_def apply transfer
  by (metis camera_core_id n_incl_def ofe_refl order_refl)

lemma persistent_split: "\<lbrakk>persistent Q; Q\<^emph>R1\<turnstile>R2; P\<^emph>Q\<turnstile>T\<rbrakk> \<Longrightarrow> P\<^emph>Q\<^emph>R1\<turnstile>T\<^emph>R2"
proof -
  assume assms: "persistent Q" "Q\<^emph>R1 \<turnstile> R2" "P\<^emph>Q\<turnstile>T"
  from upred_sep_mono[OF this(3,2)] have "P\<^emph>Q\<^emph>Q\<^emph>R1 \<turnstile> T\<^emph>R2"
    using upred_entails_trans upred_sep_assoc_rev by blast
  moreover from persistent_dupl[OF assms(1)] have "P\<^emph>Q\<^emph>R1 \<turnstile> P\<^emph>Q\<^emph>Q\<^emph>R1"
    using upred_entail_eqR upred_entails_exchange upred_frame upred_sep_assoc by blast
  ultimately show ?thesis using upred_entails_trans by blast
qed  

lemma persistent_keep: "\<lbrakk>persistent Q; P\<turnstile>Q\<rbrakk> \<Longrightarrow> P\<turnstile>P\<^emph>Q"
  unfolding persistent_def by transfer (metis camera_comm camera_core_id ofe_refl)

method pers_solver = (rule pers_rule)+
  
subsubsection \<open> Timeless predicates \<close>
definition except_zero :: "'a::ucamera upred_f \<Rightarrow> 'a upred_f" ("\<diamondop>_") where 
  "except_zero P \<equiv> P \<or>\<^sub>u \<triangleright>\<upharpoonleft>False"

lemma except_zeroI: "P \<turnstile> \<diamondop> P"
  unfolding except_zero_def by transfer blast

lemma except_zero_sep: "\<diamondop>(P \<^emph> Q) \<stileturn>\<turnstile> (\<diamondop>P) \<^emph> (\<diamondop>Q)"
  apply (auto simp: except_zero_def intro!: upred_entail_eqI; transfer)
  using n_incl_def n_incl_refl by blast+

lemma except_zero_sepR: "(\<diamondop>P) \<^emph> Q \<turnstile> \<diamondop>(P \<^emph> Q)"
  by (auto intro: upred_entails_exchange[OF except_zeroI] upred_entail_eqR[OF except_zero_sep])

lemma except_zero_sepL: "P \<^emph> (\<diamondop>Q) \<turnstile> \<diamondop>(P \<^emph> Q)"
  by (metis except_zero_sepR upred_sep_comm)
  
lemma persistent_except_zero: "persistent P \<Longrightarrow> persistent (\<diamondop>P)"
unfolding except_zero_def
apply (rule persistent_disj)
apply assumption
by (rule persistent_later[OF persistent_pure])

definition timeless :: "'a::ucamera upred_f \<Rightarrow> bool" where "timeless P \<equiv> (\<triangleright>P) \<turnstile> \<diamondop>P"

lemma own_timeless: "timeless (Own (x::'a::ducamera))"
  by (auto simp: upred_own.rep_eq upred_entails.rep_eq upred_later.rep_eq except_zero_def 
    upred_disj.rep_eq upred_pure.rep_eq n_incl_def d_equiv timeless_def)

subsubsection \<open>Plain predicates\<close>
definition plain :: "'a::ucamera upred_f \<Rightarrow> bool" where "plain P \<equiv> P\<turnstile>\<^item>P"

named_theorems plain_rule
method plain_solver = (rule plain_rule)+

lemma plain_persistent: "plain P \<Longrightarrow> persistent P" 
  unfolding plain_def persistent_def apply transfer using n_incl_\<epsilon> by blast

lemma bupd_plain_sound: "\<lbrakk>plain P; \<Rrightarrow>\<^sub>b P\<rbrakk> \<Longrightarrow> P"
  unfolding plain_def by transfer (metis \<epsilon>_right_id n_incl_\<epsilon> verit_comp_simplify1(2))

lemma plain_pure [plain_rule]: "plain (\<upharpoonleft>P)" unfolding plain_def by transfer blast
lemma plain_conj [plain_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<and>\<^sub>uQ)" unfolding plain_def by transfer fast
lemma plain_disj [plain_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<or>\<^sub>uQ)" unfolding plain_def by transfer fast
lemma plain_forall [plain_rule]: "\<forall>x. plain (P x) \<Longrightarrow> plain (\<forall>\<^sub>u x. P x)" unfolding plain_def by transfer blast
lemma plain_exists [plain_rule]: "\<forall>x. plain (P x) \<Longrightarrow> plain (\<exists>\<^sub>u x. P x)" unfolding plain_def by transfer blast
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
end