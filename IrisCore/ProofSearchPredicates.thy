theory ProofSearchPredicates
imports ProofRules
begin

subsection \<open>Predicates that guide the proof search\<close>
text \<open>These are based on type classes which the IPM uses to guide its proof search for certain steps.\<close>

named_theorems log_prog_rule "Rules that can be used for logic programming reasoning in Iris"

subsubsection \<open>Splitting\<close>
definition can_be_split :: "('a::ucamera) upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" where
  "can_be_split PQ P Q \<equiv> PQ \<stileturn>\<turnstile> P \<^emph> Q"
named_theorems split_rule
  
lemma can_be_split_refl: "can_be_split (P\<^emph>Q) P Q"
  unfolding can_be_split_def by (simp add: upred_entails_eq_eq)

lemma can_be_split_baseL: "can_be_split P P upred_emp"
  unfolding can_be_split_def by (simp add: upred_entails_eq_eq upred_true_sep)

lemma can_be_split_baseR: "can_be_split P upred_emp P"
  unfolding can_be_split_def by (simp add: upred_entails_eq_eq upred_true_sep upred_sep_comm)
  
lemma can_be_split_rev: "can_be_split P Q R \<Longrightarrow> can_be_split P R Q"
  unfolding can_be_split_def upred_entail_eq_def by (simp add: upred_sep_comm)

lemma can_be_split_mono [split_rule]: 
  "\<lbrakk>can_be_split P P1 P2; can_be_split Q Q1 Q2\<rbrakk> \<Longrightarrow> can_be_split (P\<^emph>Q) (P1\<^emph>Q1) (P2\<^emph>Q2)"
  by (smt (verit, del_insts) can_be_split_def upred_entail_eq_def upred_sep_assoc_eq 
    upred_sep_comm2_eq upred_sep_mono) 

lemma can_be_splitI: "P \<stileturn>\<turnstile> Q \<^emph> R \<Longrightarrow> can_be_split P Q R" unfolding can_be_split_def .

lemma can_be_splitE: "can_be_split P Q R \<Longrightarrow> P \<stileturn>\<turnstile> Q \<^emph> R" unfolding can_be_split_def .

lemma can_be_split_R_R: "can_be_split P P1 P2 \<Longrightarrow> can_be_split (Q\<^emph>P) P1 (Q\<^emph>P2)"
  by (metis can_be_split_mono can_be_split_refl upred_sep_comm upred_true_sep)

lemma can_be_split_sepL: "can_be_split P Q R \<Longrightarrow> can_be_split (P\<^emph>S) (Q\<^emph>S) R"
  by (simp add: can_be_split_def upred_entail_eq_def upred_frame upred_sep_comm2_eq)

lemma can_be_split_sepR: "can_be_split P Q R \<Longrightarrow> can_be_split (P\<^emph>S) Q (R\<^emph>S)"
  by (simp add: can_be_split_def upred_entail_eq_def upred_frame upred_sep_assoc_eq)

lemma split_trans: "\<lbrakk>can_be_split P P1 P2; P1 \<turnstile> Q; Q\<^emph>P2 \<turnstile> R\<rbrakk> \<Longrightarrow> P \<turnstile> R"
  unfolding can_be_split_def by (meson upred_entail_eqL upred_entails_trans upred_frame)

lemma split_trans_rule: "\<lbrakk>Q\<turnstile>Q'; can_be_split P P1 P2; P1 \<turnstile> Q; Q'\<^emph>P2 \<turnstile> R\<rbrakk> \<Longrightarrow> P \<turnstile> R"
  unfolding can_be_split_def by (meson upred_entail_eqL upred_entails_trans upred_frame)

lemma split_frame: "\<lbrakk>can_be_split P P1 P2; can_be_split Q Q1 Q2; P1\<turnstile>Q1; P2\<turnstile>Q2\<rbrakk> \<Longrightarrow> P\<turnstile>Q"
  by (meson can_be_split_def split_trans upred_entail_eqR upred_entails_refl upred_entails_trans upred_sep_mono)

lemma can_be_split_disj [split_rule]: "\<lbrakk>can_be_split P P' Q; can_be_split R R' Q\<rbrakk> \<Longrightarrow> can_be_split (P\<or>\<^sub>uR) (P'\<or>\<^sub>uR') Q"
  unfolding can_be_split_def upred_entail_eq_def by transfer blast
  
lemma can_be_split_later [split_rule]: "can_be_split P Q R \<Longrightarrow> can_be_split (\<triangleright>P) (\<triangleright>Q) (\<triangleright>R)"
  unfolding can_be_split_def by (smt (verit, ccfv_threshold) upred_later_sep upred_later_mono 
  diff_le_self ne_sprop_weaken ofe_refl upred_entail_eq_simp upred_later.rep_eq valid_raw_non_expansive)

lemma can_be_split_except_zero [split_rule]: "can_be_split P Q R \<Longrightarrow> can_be_split (\<diamondop>P) (\<diamondop>Q) (\<diamondop>R)"
  unfolding can_be_split_def using except_zero_sep except_zero_mono
  by (smt (verit, ccfv_threshold) upred_entail_eq_def upred_entails_trans)

subsubsection \<open>Framing\<close>
definition frame :: "('a::ucamera) upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" where
  "frame P Q R \<equiv> Q\<^emph>R \<turnstile> P"
named_theorems frame_rule
  
lemma frameI: "Q\<^emph>R \<turnstile> P \<Longrightarrow> frame P Q R" unfolding frame_def .
lemma frameE: "frame P Q R \<Longrightarrow> Q\<^emph>R \<turnstile> P" unfolding frame_def .

text \<open>Central lemma of framing.\<close>
lemma framing: "\<lbrakk>frame P Q R; S \<turnstile> Q\<rbrakk> \<Longrightarrow> S\<^emph>R\<turnstile>P"
  by (simp add: frame_def upred_entails_substE upred_sep_comm)

lemma framing': "\<lbrakk>can_be_split S T Q; T \<turnstile> P\<rbrakk> \<Longrightarrow> S\<turnstile>P\<^emph>Q"
  unfolding can_be_split_def upred_entail_eq_def
  using upred_entails_trans upred_frame by blast

lemma framing_emp: "\<lbrakk>frame P Q R; upred_emp \<turnstile> Q\<rbrakk> \<Longrightarrow> R\<turnstile>P"
  using frameE upred_emp_left upred_entails_trans by blast

lemma frame_refl [frame_rule,log_prog_rule]: "frame (P\<^emph>Q) P Q"
  unfolding frame_def by simp  
  
lemma frame_baseL: "frame P P upred_emp"
  unfolding frame_def by (rule upred_weakeningL)

lemma frame_baseR [frame_rule,log_prog_rule]: "frame P upred_emp P"
  unfolding frame_def by (rule upred_weakeningR)

lemma can_be_split_frame: "can_be_split P Q R \<Longrightarrow> frame P Q R"
  unfolding can_be_split_def upred_entail_eq_def frame_def by simp

lemma frame_rev: "frame P Q R \<Longrightarrow> frame P R Q"
  unfolding frame_def by (simp add: upred_sep_comm)

lemma frame_mono: "\<lbrakk>frame P1 Q1 R1; frame P2 Q2 R2\<rbrakk> \<Longrightarrow> frame (P1\<^emph>P2) (Q1\<^emph>Q2) (R1\<^emph>R2)"
proof-
assume "frame P1 Q1 R1" "frame P2 Q2 R2"
from upred_sep_mono[OF this[unfolded frame_def]] show "frame (P1\<^emph>P2) (Q1\<^emph>Q2) (R1\<^emph>R2)" 
  by (simp add: upred_sep_comm2_eq frame_def upred_sep_assoc_eq)
qed

lemma frame_sepL [frame_rule,log_prog_rule]: "frame P Q R \<Longrightarrow> frame (P\<^emph>S) (Q\<^emph>S) R"
  by (simp add: frame_def upred_frame upred_sep_comm2_eq)

lemma frame_sepR: "frame P Q R \<Longrightarrow> frame (P\<^emph>S) Q (R\<^emph>S)"
  by (simp add: frame_def upred_frame upred_sep_assoc_eq)

lemma frame_disj [frame_rule,log_prog_rule]: "\<lbrakk>frame P P' Q; frame R R' Q\<rbrakk> \<Longrightarrow> frame (P\<or>\<^sub>uR) (P'\<or>\<^sub>uR') Q"
  unfolding frame_def by transfer metis

method frame_solver = (rule frame_rule)+
  
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

lemma persistent_persis [pers_rule,log_prog_rule]: "persistent (\<box>P)"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq camera_core_idem)

lemma persistent_pure [pers_rule,log_prog_rule]: "persistent (\<upharpoonleft>P)"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_pure.rep_eq)  

lemma persistent_valid [pers_rule,log_prog_rule]: "persistent (\<V>(a))"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_valid.rep_eq)
  
lemma persistent_core_own [pers_rule,log_prog_rule]: "persistent (Own(a::'a::{core_id,ucamera}))"
  by (auto simp: persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_own.rep_eq core_id)

lemma persistent_core_own2 [pers_rule,log_prog_rule]: "pcore_id_pred (a::'a::ucamera) \<Longrightarrow> persistent (Own a)"
  unfolding persistent_def upred_persis.rep_eq upred_entails.rep_eq upred_own.rep_eq core_id_pred
  using camera_core_mono_n by fastforce

lemma persistent_eq [pers_rule,log_prog_rule]: "persistent (a=\<^sub>ub)"
  unfolding persistent_def by transfer simp

lemma persistent_later [pers_rule,log_prog_rule]: "persistent P \<Longrightarrow> persistent (\<triangleright> P)"
  unfolding persistent_def
  by (rule upred_entails_trans[OF upred_later_mono[of P "\<box>P"] upred_entail_eqR[OF upred_persis_later]])

lemma persistent_conj [pers_rule,log_prog_rule]: "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P \<and>\<^sub>u Q)"
  by (auto simp: persistent_def upred_conj.rep_eq upred_entails.rep_eq upred_persis.rep_eq)

lemma persistent_disj [pers_rule,log_prog_rule]: "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P \<or>\<^sub>u Q)"
  by (auto simp: persistent_def upred_disj.rep_eq upred_entails.rep_eq upred_persis.rep_eq)
  
lemma persistent_exists [pers_rule,log_prog_rule]: "(\<And>x. persistent (P x)) \<Longrightarrow> persistent (\<exists>\<^sub>u x. P x)"
  by (auto simp: upred_exists.rep_eq persistent_def upred_persis.rep_eq upred_entails.rep_eq)

lemma persistent_forall [pers_rule,log_prog_rule]: "(\<And>x. persistent (P x)) \<Longrightarrow> persistent (\<forall>\<^sub>u x. P x)"
  by (auto simp: upred_forall.rep_eq persistent_def upred_persis.rep_eq upred_entails.rep_eq)

lemma persistent_sep [pers_rule,log_prog_rule]: "\<lbrakk>persistent P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P \<^emph> Q)"
by (simp add: persistent_def upred_sep.rep_eq upred_entails.rep_eq upred_persis.rep_eq)
  (metis camera_comm camera_core_id camera_valid_op dual_order.refl n_incl_def ofe_refl 
    upred_def_def upred_def_rep)

lemma persistent_except_zero [pers_rule,log_prog_rule]: "persistent P \<Longrightarrow> persistent (\<diamondop>P)"
  unfolding except_zero_def
  apply (pers_solver, assumption)
  by pers_solver
  
lemma persistent_dupl: "persistent P \<Longrightarrow> P\<^emph>P \<stileturn>\<turnstile> P"
  unfolding persistent_def upred_entail_eq_def 
  by transfer (metis camera_core_id n_incl_def ofe_refl order_refl)

lemma persistent_dupl': "persistent P \<Longrightarrow> can_be_split P P P"
  unfolding can_be_split_def using persistent_dupl upred_entail_eq_symm by blast
lemmas persistent_dupl_frame = can_be_split_frame[OF persistent_dupl']
  
lemma persistent_dupl_split: "persistent P \<Longrightarrow> can_be_split (Q\<^emph>P) (Q\<^emph>P) P"
  unfolding can_be_split_def using persistent_dupl upred_entail_eq_def upred_entails_substE 
  upred_sep_assoc upred_weakeningL by blast
lemmas persistent_dupl_frame2 = can_be_split_frame[OF persistent_dupl_split]
  
lemma persistent_dupl_split': "\<lbrakk>persistent P; can_be_split Q R S\<rbrakk> \<Longrightarrow> can_be_split (Q\<^emph>P) (R\<^emph>P) (S\<^emph>P)"
  unfolding can_be_split_def using can_be_split_def can_be_split_mono persistent_dupl' by blast

lemma persistent_dupl_frame3: "\<lbrakk>persistent P; frame Q R S\<rbrakk> \<Longrightarrow> frame (Q\<^emph>P) (R\<^emph>P) (S\<^emph>P)"
  unfolding frame_def using frameE frameI frame_mono persistent_dupl_frame by blast

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

subsubsection \<open>Except zero predicates\<close>
definition is_except_zero :: "'a::ucamera upred_f \<Rightarrow> bool" where "is_except_zero P \<equiv> \<diamondop>P \<turnstile> P"
named_theorems iez_rule
method iez_solver = (rule iez_rule)+

lemma is_except_zero_except_zero [iez_rule,log_prog_rule]: "is_except_zero (\<diamondop>P)"
  unfolding is_except_zero_def by (rule except_zero_idem)

lemma is_except_zero_later [iez_rule,log_prog_rule]: "is_except_zero (\<triangleright>P)"
  unfolding is_except_zero_def except_zero_def by transfer blast

subsubsection \<open>Timeless predicates\<close>
definition timeless :: "'a::ucamera upred_f \<Rightarrow> bool" where "timeless P \<equiv> (\<triangleright>P) \<turnstile> \<diamondop>P"

named_theorems timeless_rule
method timeless_solver = (rule timeless_rule)+

lemma own_timeless' [timeless_rule,log_prog_rule]: "dcamera_val x \<Longrightarrow> timeless (Own x)"
  apply (auto simp: timeless_def dcamera_val_def discrete_val_def except_zero_def; transfer) 
  apply (auto simp: n_incl_def)
  apply (metis (mono_tags, lifting) Rep_sprop bot_nat_0.extremum camera_valid_op diff_le_self mem_Collect_eq n_valid_ne)
  by (metis camera_extend diff_le_self ne_sprop_weaken ofe_eq_limit ofe_sym valid_raw_non_expansive)

lemma own_timeless [timeless_rule,log_prog_rule]: "timeless (Own (x::'a::ducamera))"
  by (auto simp: upred_own.rep_eq upred_entails.rep_eq upred_later.rep_eq except_zero_def 
    upred_disj.rep_eq upred_pure.rep_eq n_incl_def d_equiv timeless_def)

lemma timeless_pure [timeless_rule,log_prog_rule]: "timeless (\<upharpoonleft>(b))"
  unfolding timeless_def except_zero_def by transfer simp

lemma timeless_conj [timeless_rule,log_prog_rule]: "\<lbrakk>timeless P; timeless Q\<rbrakk> \<Longrightarrow> timeless (P\<and>\<^sub>uQ)"
  unfolding timeless_def except_zero_def by transfer blast

lemma timeless_disj [timeless_rule]: "\<lbrakk>timeless P; timeless Q\<rbrakk> \<Longrightarrow> timeless (P\<or>\<^sub>uQ)"
  unfolding timeless_def except_zero_def by transfer blast

lemma timeless_impl [timeless_rule,log_prog_rule]: "timeless Q \<Longrightarrow> timeless (P\<longrightarrow>\<^sub>uQ)"
  unfolding timeless_def except_zero_def apply transfer
  by (metis (mono_tags, lifting) Rep_sprop diff_le_mono diff_le_self diff_self_eq_0 mem_Collect_eq n_incl_refl)

lemma timeless_sep [timeless_rule,log_prog_rule]: "\<lbrakk>timeless P; timeless Q\<rbrakk> \<Longrightarrow> timeless (P\<^emph>Q)"
  unfolding timeless_def 
  apply (rule upred_entails_trans[OF upred_entail_eqL[OF upred_later_sep]])
  apply (rule upred_entails_trans[OF _ upred_entail_eqR[OF except_zero_sep]])
  by (auto intro: upred_sep_mono)

lemma timeless_wand [timeless_rule,log_prog_rule]: "timeless Q \<Longrightarrow> timeless (P-\<^emph>Q)"
  unfolding timeless_def except_zero_def apply transfer
  by (smt (verit, ccfv_threshold) Rep_sprop diff_diff_cancel diff_is_0_eq diff_right_commute 
    mem_Collect_eq n_incl_refl nat_le_linear)

lemma timeless_forall [timeless_rule,log_prog_rule]: "(\<And>x. timeless (P x)) \<Longrightarrow> timeless (\<forall>\<^sub>u x. P x)"
  unfolding timeless_def except_zero_def by transfer' blast

lemma timeless_exists [timeless_rule,log_prog_rule]: "(\<And>x. timeless (P x)) \<Longrightarrow> timeless (\<exists>\<^sub>u x. P x)"
  unfolding timeless_def except_zero_def by transfer' blast

lemma timeless_persis [timeless_rule,log_prog_rule]: "timeless P \<Longrightarrow> timeless (\<box>P)"
  unfolding timeless_def except_zero_def apply transfer using camera_core_n_valid by blast

subsubsection \<open>Modality elimination\<close>
definition elim_modal :: "'a::ucamera upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> 'a upred_f \<Rightarrow> bool" 
  where "elim_modal P P' Q Q' \<equiv> P \<^emph> (P'-\<^emph>Q') \<turnstile> Q"
  
lemma elim_modal_timeless: "\<lbrakk>P \<turnstile> \<diamondop>P'; is_except_zero Q\<rbrakk> \<Longrightarrow> elim_modal P P' Q Q"
  unfolding is_except_zero_def elim_modal_def
  by (metis except_zero_mono_ext upred_entails_refl upred_entails_trans upred_frame upred_sep_comm upred_wandE)

lemma elim_modal_timeless': "\<lbrakk>timeless P; is_except_zero Q\<rbrakk> \<Longrightarrow> elim_modal (\<triangleright>P) P Q Q"
  by (unfold timeless_def;rule elim_modal_timeless;assumption+)

lemma elim_later_timelessL: "timeless P \<Longrightarrow> elim_modal (\<triangleright>P) P (\<triangleright>Q) (\<triangleright>Q)"
  by (rule elim_modal_timeless', assumption, iez_solver)

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

lemma plain_persistent [log_prog_rule]: "plain P \<Longrightarrow> persistent P" 
  unfolding plain_def persistent_def apply transfer using n_incl_\<epsilon> by blast

lemma bupd_plain_sound: "\<lbrakk>plain P; \<Rrightarrow>\<^sub>b P\<rbrakk> \<Longrightarrow> P"
  unfolding plain_def by transfer (metis \<epsilon>_right_id n_incl_\<epsilon> verit_comp_simplify1(2))

lemma bupd_plain: "plain P \<Longrightarrow> \<Rrightarrow>\<^sub>b P \<turnstile> P"
  unfolding plain_def by transfer (metis \<epsilon>_right_id n_incl_\<epsilon> order_refl)

lemma plain_pure [plain_rule,log_prog_rule]: "plain (\<upharpoonleft>P)" unfolding plain_def by transfer blast
lemma plain_conj [plain_rule,log_prog_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<and>\<^sub>uQ)" unfolding plain_def by transfer fast
lemma plain_disj [plain_rule,log_prog_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<or>\<^sub>uQ)" unfolding plain_def by transfer fast
lemma plain_forall [plain_rule,log_prog_rule]: "(\<And>x. plain (P x)) \<Longrightarrow> plain (\<forall>\<^sub>u x. P x)" 
  unfolding plain_def by transfer blast
lemma plain_exists [plain_rule,log_prog_rule]: "(\<And>x. plain (P x)) \<Longrightarrow> plain (\<exists>\<^sub>u x. P x)" 
  unfolding plain_def by transfer blast
lemma plain_impl [plain_rule,log_prog_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<longrightarrow>\<^sub>uQ)" 
  unfolding plain_def apply transfer
  by (smt (verit, ccfv_threshold) Rep_sprop \<epsilon>_right_id incl_def mem_Collect_eq n_incl_\<epsilon> order_refl)
lemma plain_wand [plain_rule,log_prog_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P-\<^emph>Q)"
  unfolding plain_def apply transfer
  by (metis (mono_tags, lifting) Rep_sprop \<epsilon>_left_id \<epsilon>_right_id mem_Collect_eq n_incl_op_extend order_refl)
lemma plain_sep [plain_rule,log_prog_rule]: "\<lbrakk>plain P; plain Q\<rbrakk> \<Longrightarrow> plain (P\<^emph>Q)" 
  unfolding plain_def apply transfer
  by (metis \<epsilon>_left_id camera_comm n_incl_def ofe_refl order_refl)  
lemma plain_plainly [plain_rule,log_prog_rule]: "plain (\<^item>P)" unfolding plain_def by transfer fast
lemma plain_eq [plain_rule,log_prog_rule]: "plain (a=\<^sub>ub)" unfolding plain_def by transfer blast
lemma plain_later [plain_rule,log_prog_rule]: "plain P \<Longrightarrow> plain (\<triangleright>P)" 
  unfolding plain_def apply transfer using Rep_sprop diff_le_self by blast
lemma plain_except_zero [plain_rule,log_prog_rule]: "plain P \<Longrightarrow> plain (\<diamondop>P)" unfolding except_zero_def
  by (plain_solver, assumption)+  plain_solver

method pers_solver' = (pers_solver; rule plain_persistent; plain_solver)

lemma persistent_impl: "\<lbrakk>plain P; persistent Q\<rbrakk> \<Longrightarrow> persistent (P -\<^emph> Q)"
  unfolding plain_def persistent_def apply transfer
  by (metis (no_types, lifting) \<epsilon>_right_id camera_comm n_incl_op_extend ne_sprop_weaken ofe_eq_limit 
    order_eq_refl valid_raw_non_expansive)
end