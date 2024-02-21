theory WorldSatisfaction
imports Misc Namespace View
begin           

subsection \<open>Invariants\<close>

subsubsection \<open>World satisfaction\<close>
text \<open> 
  Impredicative invariants are formalized as propositions which are managed by the so called
  World Satisfaction. It holds a map of named invariants and keeps track which of them are opened 
  (i.e. enabled/can be used thread-locally and might not hold) and which are closed 
  (i.e. disabled/hold for all threads).
\<close>
text \<open>Arbitrary but unique names for singleton cameras\<close>
definition "invariant_name :: gname \<equiv> 1" 
definition "enabled_name :: gname \<equiv> 2" 
definition "disabled_name :: gname \<equiv> 3"

type_synonym inv = "(name, pre_iprop later) map_view \<times> name dset \<times> name dfset"

context 
fixes get_inv :: "gname \<Rightarrow> 'res::ucamera \<Rightarrow> inv option"
  and upd_inv
assumes inv_inG: "inG get_inv upd_inv"
begin

definition own_inv :: "gname \<Rightarrow> inv \<Rightarrow> 'res upred_f" ("Own\<^sub>i _ _") where
  "own_inv \<gamma> i = own upd_inv \<gamma> i"

text \<open>Allocate new invariant map\<close>
definition ownI :: "name \<Rightarrow> 'res upred_f \<Rightarrow> 'res upred_f" where
  "ownI \<iota> P = Own\<^sub>i invariant_name (map_view_frag \<iota> DfracDiscarded (Next (pre P)),\<epsilon>,\<epsilon>)"

definition inv_raw :: "namespace \<Rightarrow> 'res upred_f \<Rightarrow>  'res upred_f" where
  "inv_raw N P \<equiv> \<exists>\<^sub>u \<iota>. ((\<upharpoonleft>(\<iota>\<in>\<^sub>d dnames N)) \<and>\<^sub>u ownI \<iota> P)"

text \<open>Allocate new enabled invariant map\<close>
definition ownE :: "name set \<Rightarrow> 'res upred_f" where
  "ownE E = Own\<^sub>i enabled_name (\<epsilon>,DSet E,\<epsilon>)"

text \<open>Allocate new disabled invariant map\<close>
definition ownD :: "name fset \<Rightarrow> 'res upred_f" where
  "ownD D = Own\<^sub>i disabled_name (\<epsilon>,\<epsilon>,DFSet D)"
  
definition lift_inv_fmap :: "(name,'res upred_f) fmap \<Rightarrow> (name, pre_iprop later) fmap" where
  "lift_inv_fmap m = Abs_fmap (map_option (Next \<circ> pre) \<circ> (fmlookup m))"

lemma lift_inf_fmap_finite: "(map_option (Next \<circ> pre) \<circ> (fmlookup m)) \<in> {m. finite (dom m)}"
  by auto

text \<open>World satisfaction, i.e. the invariant that holds all invariants\<close>
definition wsat :: "'res upred_f" where
  "wsat \<equiv> \<exists>\<^sub>u (I::(name,'res upred_f) fmap).
    ((Own\<^sub>i invariant_name (map_view_auth (DfracOwn 1) (lift_inv_fmap I),\<epsilon>,\<epsilon>))
    \<^emph> (sep_map_fmdom (\<lambda>\<iota>. (\<triangleright>(the (fmlookup I \<iota>))) \<^emph> ownD {|\<iota>|} \<or>\<^sub>u (ownE {\<iota>})) I)
  )"

lemma own_inv_ne [upred_ne_rule]: "\<lbrakk>n_equiv n \<gamma>1 \<gamma>2; n_equiv n i j\<rbrakk> \<Longrightarrow> n_equiv n (Own\<^sub>i \<gamma>1 i) (Own\<^sub>i \<gamma>2 j)"
  apply (auto simp: own_inv_def n_equiv_fun_def ofe_refl n_equiv_option_def intro!: upred_ne_rule)
  using inG.own_ne inv_inG by blast

lemma ownI_ne [upred_ne_rule]: "\<lbrakk>n_equiv n n1 n2; n_equiv n P Q\<rbrakk> \<Longrightarrow> n_equiv n (ownI n1 P) (ownI n2 Q)"
apply (auto simp: ownI_def ofe_refl n_equiv_map_view_def map_view_auth_proj_def map_view_frag_proj_def 
  map_view_frag_def mview_frag_def n_equiv_fun_def n_equiv_option_def n_equiv_ag.rep_eq to_ag.rep_eq 
  n_equiv_later_def intro!: upred_ne_rule split: map_view.splits)
  using non_expansiveE[OF ipropIso.to_ne] diff_le_self ofe_mono by blast

lemma inv_raw_ne [upred_ne_rule]: "\<lbrakk>n_equiv n N M; n_equiv n P Q\<rbrakk> \<Longrightarrow> n_equiv n (inv_raw N P) (inv_raw M Q)"
  by (auto simp: inv_raw_def intro!: upred_ne_rule)

lemma inv_ownE_ne [upred_ne_rule]: "n_equiv n N M \<Longrightarrow> n_equiv n (ownE N) (ownE M)"
  by (auto simp: ownE_def ofe_refl n_equiv_dset_def d_equiv intro!: upred_ne_rule)

lemma inv_ownD_ne [upred_ne_rule]: "n_equiv n N M \<Longrightarrow> n_equiv n (ownD N) (ownD M)"
  by (auto simp: ownD_def ofe_refl n_equiv_dfset_def d_equiv intro!: upred_ne_rule)
  
lemma pcore_id_inv: "pcore_id_pred (map_view_frag \<iota> DfracDiscarded (Next (pre P)), \<epsilon>, \<epsilon>)"
  unfolding prod_pcore_id_pred apply (simp add: \<epsilon>_pcore_id_def)
  by (meson discarded_core_id pcore_id_frag)

lemma persistent_ownI [pers_rule,log_prog_rule]: "persistent (ownI \<iota> P)"
unfolding ownI_def own_inv_def by (rule persistent_core_own2[OF inv_inG, OF pcore_id_inv])

lemma persistent_inv_raw [pers_rule,log_prog_rule]: "persistent (inv_raw N P)"
  unfolding inv_raw_def
  apply (rule persistent_exists)
  apply (rule persistent_conj)
  apply (rule persistent_pure)
  by (rule persistent_ownI)

lemma put_inv_valid: "\<lbrakk>valid mv; valid e; valid d\<rbrakk> \<Longrightarrow> valid (inG.return_cmra upd_inv \<gamma> (mv,e,d))"
  by (auto simp: valid_def inG.return_n_valid[OF inv_inG] valid_raw_prod_def sprop_conj.rep_eq)

lemma ownE_singleton_twice: "ownE {i} \<^emph> ownE {i} \<turnstile> \<upharpoonleft>False"
  unfolding ownE_def own_inv_def
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF inG.own_op[OF inv_inG]]])
  apply (rule upred_entails_trans[OF inG.own_valid[OF inv_inG]])
  apply (simp add: op_prod_def \<epsilon>_left_id op_dset_def)
  apply transfer
  by (auto simp: prod_n_valid_def \<epsilon>_n_valid valid_raw_dset_def)  
  
lemma ownD_singleton_twice: "ownD {|i|} \<^emph> ownD {|i|} \<turnstile> \<upharpoonleft>False"
  unfolding ownD_def own_inv_def inG.own_def[OF inv_inG]
  apply (auto simp: op_prod_def \<epsilon>_left_id op_dfset_def inG.return_op[OF inv_inG, symmetric]
    intro!: upred_entails_trans[OF upred_entail_eqR[OF upred_own_op]] upred_entails_trans[OF upred_own_valid])
  apply (rule upred_entails_trans[OF upred_entail_eqL[OF inG.valid_get[OF inv_inG]]])
  apply transfer
  by (simp add: prod_n_valid_def \<epsilon>_n_valid valid_raw_dfset_def)
  
lemma ownE_op: "E1 \<inter> E2 = {} \<Longrightarrow> ownE (E1 \<union> E2) \<stileturn>\<turnstile> ownE E1 \<^emph> ownE E2"
proof -
  assume "E1 \<inter> E2 = {}"
  then have un_op:"DSet (E1 \<union> E2) = DSet E1 \<cdot> DSet E2" unfolding op_dset_def by simp
  from inG.own_op[OF inv_inG, of "enabled_name" "(\<epsilon>,DSet E1,\<epsilon>)" "(\<epsilon>,DSet E2,\<epsilon>)"]
  show ?thesis by (auto simp: ownE_def own_inv_def un_op op_prod_def \<epsilon>_left_id)
qed

lemma ownE_op': "(\<upharpoonleft>(E1 \<inter> E2 = {})) \<and>\<^sub>u ownE (E1 \<union> E2) \<stileturn>\<turnstile> ownE E1 \<^emph> ownE E2"
  apply (auto simp: upred_entail_eq_def)
  apply (subst upred_conj_comm)
  apply (auto intro!: upred_pure_impl' upred_entail_eqL[OF ownE_op])
  apply (auto simp: ownE_def own_inv_def op_prod_def \<epsilon>_left_id inG.own_def[OF inv_inG]
    inG.return_op[OF inv_inG,symmetric] intro!: upred_entails_trans[OF upred_entail_eqR[OF upred_own_op]])
  apply (auto simp: upred_entails.rep_eq upred_own.rep_eq upred_pure.rep_eq upred_conj.rep_eq)
  proof -
  fix a n x
  assume assms: "n_valid a n" "x \<in> E1" "x \<in> E2" "n_incl n (inG.return_cmra upd_inv enabled_name
    (\<epsilon>, DSet E1 \<cdot> DSet E2, \<epsilon>)) a"
  then have "n_valid (inG.return_cmra upd_inv enabled_name (\<epsilon>, DSet E1 \<cdot> DSet E2, \<epsilon>)) n"
    using n_valid_ne camera_valid_op n_incl_def by blast
  then have "n_valid (DSet E1 \<cdot> DSet E2) n"
    by (auto simp: inG.return_n_valid[OF inv_inG] prod_n_valid_def)
  with assms(2,3) show False apply (auto simp: valid_raw_dset_def op_dset_def)
    by (smt (verit, best) Int_iff dset.simps(5) empty_iff sPure.rep_eq)
  next
  fix a n
  assume assms: "n_valid a n" "n_incl n (inG.return_cmra upd_inv enabled_name (\<epsilon>, DSet E1 \<cdot> DSet E2, \<epsilon>)) a"
  then have "n_valid (inG.return_cmra upd_inv enabled_name (\<epsilon>, DSet E1 \<cdot> DSet E2, \<epsilon>)) n"
  using n_valid_ne camera_valid_op n_incl_def by blast
  then have "n_valid (DSet E1 \<cdot> DSet E2) n"
    by (auto simp: inG.return_n_valid[OF inv_inG] prod_n_valid_def)
  then have "(DSet E1 \<cdot> DSet E2) = DSet (E1 \<union> E2)" apply (auto simp: op_dset_def valid_raw_dset_def)
    by (smt (verit, best) Int_iff dset.simps(5) empty_iff sPure.rep_eq)
  with assms(2) show "n_incl n (inG.return_cmra upd_inv enabled_name (\<epsilon>, DSet (E1 \<union> E2), \<epsilon>)) a" by simp
qed
  
lemma ownE_op_minus: "E1 \<subseteq> E2 \<Longrightarrow> ownE (E1 \<union> (E2-E1)) \<stileturn>\<turnstile> ownE E1 \<^emph> ownE (E2-E1)"
proof -
  assume "E1 \<subseteq> E2"
  then have "E1 \<inter> (E2-E1) = {}" by simp
  from ownE_op[OF this] show ?thesis .
qed
  
lemma auth_map_both_validI: 
  "\<V>(inG.return_cmra upd_inv \<gamma> (map_view_auth (DfracOwn 1) m,\<epsilon>,\<epsilon>) 
    \<cdot> inG.return_cmra upd_inv \<gamma> (map_view_frag k dq v,\<epsilon>,\<epsilon>)) \<turnstile>
    (fmlookup m k =\<^sub>u Some v) \<and>\<^sub>u \<upharpoonleft>(valid dq)"
unfolding inG.return_op[OF inv_inG,symmetric]
apply (rule upred_entails_trans[OF upred_entail_eqL[OF inG.valid_get[OF inv_inG]]])
unfolding op_prod_def
apply (simp add: \<epsilon>_left_id auth_comb_opL op_prod_def split: prod.splits)
apply transfer'
apply (simp add: prod_n_valid_def \<epsilon>_n_valid valid_raw_option_def \<epsilon>_option_def)
using map_view_both_valid by metis

lemma invariant_lookup: 
  "Own\<^sub>i invariant_name (map_view_auth (DfracOwn 1) (lift_inv_fmap I),\<epsilon>,\<epsilon>) \<^emph> ownI \<iota> P \<turnstile> 
  (\<exists>\<^sub>u Q. \<upharpoonleft>(fmlookup I \<iota> = Some Q) \<^emph> \<triangleright>(Q=\<^sub>uP))"
  unfolding ownI_def own_inv_def inG.own_def[OF inv_inG]
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF upred_own_op]])
  apply (rule upred_entails_trans[OF upred_own_valid])
  apply (rule upred_entails_trans[OF auth_map_both_validI])
  apply (auto simp: lift_inv_fmap_def valid_raw_dfrac_def valid_def n_equiv_option_def 
     Abs_fmap_inverse[OF lift_inf_fmap_finite] emp_rule)
  apply (rule upred_entails_trans[OF upred_entail_eqL[OF option_equivI]])
  apply (auto simp: upred_exists_eq_sep' split: option.splits)
  apply (rule upred_entails_trans[OF upred_entail_eqL[OF later_equivI]])
  apply (rule upred_later_mono)
  apply transfer
  by (auto simp: ipropIso.to_equiv)

lemma lookup_pers [pers_rule,log_prog_rule]: "persistent (\<exists>\<^sub>u Q. \<upharpoonleft>(fmlookup I \<iota> = Some Q) \<^emph> \<triangleright>(Q=\<^sub>uP))"
  by pers_solver

lemma ownI_open: "wsat \<^emph> ownI i P \<^emph> ownE {i} \<turnstile> wsat \<^emph> (\<triangleright>P) \<^emph> ownD {|i|}"
unfolding wsat_def
apply (rule pull_exists_antecedent2)
apply (rule upred_existsE')
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF upred_sep_assoc])
apply (rule upred_entails_trans[OF upred_sep_assoc'])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_assoc_rev])
apply (rule upred_entails_substE[OF  persistent_keep[OF lookup_pers invariant_lookup]])
apply (rule upred_entails_trans[OF upred_sep_assoc])
apply (rule pull_exists_antecedentR)
apply (rule upred_existsE')
apply (rule upred_entails_trans[OF upred_sep_assoc])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF upred_sep_assoc])
apply (rule upred_pure_impl)
apply (rule upred_entails_trans[OF upred_sep_assoc])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (rule upred_entails_trans[OF upred_sep_assoc])+
apply (simp add: sep_map_dom_delete)
apply (rule upred_entails_trans[OF upred_sep_assoc])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_disjE')
subgoal for I Q
  apply (rule upred_entails_trans[OF upred_sep_assoc])
  apply (rule upred_frame)
  apply (rule upred_entails_trans[OF upred_sep_comm4_2])
  apply (rule upred_entails_trans[OF upred_sep_comm3M])
  apply (rule persistent_split[OF persistent_later[OF persistent_eq]])
  subgoal
    apply (rule upred_entails_trans[OF upred_entail_eqR[OF upred_later_sep]])
    apply (rule upred_later_mono)
    apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
    apply (simp add: upred_eq_comm)
    apply (rule upred_eqE)
  by simp
  apply(rule upred_existsI[of _ _ "I"])
  apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
  apply (rule upred_entails_trans[OF upred_sep_assoc])
  apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
  apply (rule upred_entails_trans[OF upred_sep_assoc])+
  apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
  apply (rule upred_entails_trans[OF upred_sep_assoc])+
  apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
  apply (rule upred_entails_trans[OF upred_sep_assoc])
  apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm]])
  apply (rule upred_frame)
  apply (simp add: sep_map_dom_delete)
  apply (rule upred_entails_trans[OF upred_sep_assoc])+
  apply (rule upred_entails_trans[OF upred_sep_comm2R])
  apply (rule upred_frame)
  apply (rule upred_disjIR)
  apply (rule upred_entails_trans[OF upred_sep_comm2R])
by (rule upred_weakeningR)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_assoc'])
apply (rule upred_entails_trans[OF upred_sep_assoc_rev])
apply (rule upred_entails_substE[OF ownE_singleton_twice])
by simp

lemma ownI_close: "wsat \<^emph> ownI i P \<^emph> (\<triangleright> P) \<^emph> ownD {|i|} \<turnstile> wsat \<^emph> ownE {i}"
apply (simp add: wsat_def)
apply (auto simp: pull_exists_eq intro!: upred_existsE')
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (auto simp: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (auto simp: upred_sep_assoc_eq)
apply (rule upred_entails_substE[OF persistent_keep[OF lookup_pers invariant_lookup], unfolded upred_sep_assoc_eq])
subgoal for I 
apply (auto simp: upred_sep_assoc_eq intro!: upred_existsI[of _ _ I] pull_exists_antecedentR upred_existsE')
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: sep_map_dom_delete upred_sep_assoc_eq intro!: upred_pure_impl)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm]])
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: upred_sep_assoc_eq intro!: upred_disjE')
subgoal for Q  
  apply (rule upred_entails_trans[OF upred_sep_comm6_2R])
  by (auto intro!: upred_entails_substE[OF ownD_singleton_twice, unfolded upred_sep_assoc_eq])
apply (auto simp: upred_sep_assoc_eq intro!: upred_frame)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto simp: upred_sep_assoc_eq intro!: upred_frame)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (simp add: upred_sep_assoc_eq)
apply (rule upred_entails_trans[OF upred_sep_comm4_2])
apply (rule upred_entails_trans[OF upred_sep_comm3M])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (rule upred_entails_trans[OF _ upred_entails_eq[OF upred_sep_comm]])
apply (auto simp: upred_sep_assoc_eq intro!: upred_frame upred_disjIL)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
by (auto intro!: upred_entails_trans[OF upred_weakeningR2] 
  upred_entails_trans[OF upred_entail_eqR[OF upred_later_sep]] upred_later_mono upred_eqE)
done

lemma ownI_alloc: "(\<forall>E::name fset. \<exists>i. \<not>i|\<in>|E \<and> \<phi> i) \<Longrightarrow> 
  (wsat \<^emph> \<triangleright> P) ==\<^emph> (\<exists>\<^sub>u i. \<upharpoonleft>(\<phi> i) \<^emph> wsat \<^emph> ownI i P)"
apply (auto simp: wsat_def pull_exists_eq intro!: upred_wand_holdsI upred_existsE')
apply (rule add_holds[OF upred_own_unit,unfolded bupd_emp[OF upred_own_nothing_emp_eq]])
apply (rule upred_entails_substE[OF upred_wand_holdsE[OF upred_own_updateP]])
sorry (* Axiomatized as this requires too much low level ghost state reasoning for which I'd need to add
    way more lemmata and things. *)

lemma ownI_alloc_open: "(\<forall>E::name fset. \<exists>i. \<not>i|\<in>|E \<and> \<phi> i) \<Longrightarrow> 
  wsat ==\<^emph> (\<exists>\<^sub>u i. \<upharpoonleft>(\<phi> i) \<^emph> (ownE {i} -\<^emph> wsat) \<^emph> ownI i P \<^emph> ownD {|i|})"
apply (auto simp: wsat_def pull_exists_eq intro!: upred_wand_holdsI upred_existsE')
sorry (* Axiomatized as this requires too much low level ghost state reasoning for which I'd need to add
    way more lemmata and things. *)

lemma wsat_alloc: "\<Rrightarrow>\<^sub>b (\<exists>\<^sub>u _:: inv. wsat \<^emph> ownE UNIV)"
apply (auto simp: upred_holds_entails)
apply (rule inG.add_own[OF inv_inG, where ?\<gamma> ="invariant_name" and ?a="(map_view_auth (DfracOwn 1) fmempty,\<epsilon>,\<epsilon>)",
  OF prod_validI[OF map_view_auth_valid prod_validI[OF \<epsilon>_valid \<epsilon>_valid]]])
apply (rule inG.add_own[OF inv_inG, where ?\<gamma> = "enabled_name" and ?a = "(\<epsilon>,DSet UNIV,\<epsilon>)", 
  OF prod_validI[OF \<epsilon>_valid prod_validI[OF _ \<epsilon>_valid]]])
apply (simp add: valid_raw_dset_def valid_def)
apply (rule inG.add_own[OF inv_inG, where ?\<gamma> = "disabled_name" and ?a = "(\<epsilon>,\<epsilon>,DFSet {||})", 
  OF prod_validI[OF \<epsilon>_valid prod_validI[OF \<epsilon>_valid _]], unfolded \<epsilon>_dfset_def[symmetric], OF \<epsilon>_valid])
apply (auto simp: wsat_def pull_exists_eq own_inv_def ownE_def ownD_def 
  intro!: upred_entails_trans[OF _ updI])
apply (rule upred_existsI[of _ _ fmempty])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto intro!: upred_frame)
apply (auto simp: lift_inv_fmap_def fmempty.rep_eq fmempty_def[symmetric] sep_fold_fset_def 
  comp_fun_commute.ffold_empty[OF sep_P_comp_fun_commute]  intro!: upred_frame)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
by (auto simp: upred_weakeningL intro!: upred_frame)
end
end