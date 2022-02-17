theory WorldSatisfaction
imports Misc
begin

subsection \<open>Invariants\<close>

subsubsection \<open>World satisfaction\<close>
text \<open> 
  Impredicative invariants are formalized as propositions which are managed by the so called
  World Satisfaction. It holds a map of named invariants and keeps track which of them are opened 
  (i.e. enabled/can be used thread-locally and might not hold) and which are closed 
  (i.e. disabled/hold for all threads).
\<close>

definition own_inv :: "inv \<Rightarrow> iprop" ("Own\<^sub>i _") where
  "own_inv i = Own(constr_inv i)"

text \<open>Allocate new invariant map\<close>
definition ownI :: "name \<Rightarrow> iprop \<Rightarrow> iprop" where
  "ownI \<iota> P = Own\<^sub>i (map_view_frag \<iota> DfracDiscarded (Next (pre P)),\<epsilon>,\<epsilon>)"

definition inv_raw :: "namespace \<Rightarrow> iprop \<Rightarrow>  iprop" where
  "inv_raw N P \<equiv> \<exists>\<^sub>u \<iota>. ((\<upharpoonleft>(\<iota>\<in>\<^sub>d dnames N)) \<and>\<^sub>u ownI \<iota> P)"

text \<open>Allocate new enabled invariant map\<close>
definition ownE :: "name set \<Rightarrow> iprop" where
  "ownE E = Own\<^sub>i (\<epsilon>,DSet E,\<epsilon>)"

text \<open>Allocate new disabled invariant map\<close>
definition ownD :: "name fset \<Rightarrow> iprop" where
  "ownD D = Own\<^sub>i (\<epsilon>,\<epsilon>,DFSet D)"
  
definition lift_inv_fmap :: "(name,iprop) fmap \<Rightarrow> (name,pre_iprop later) fmap" where
  "lift_inv_fmap m = Abs_fmap (map_option (Next \<circ> pre) \<circ> (fmlookup m))"

lemma lift_inf_fmap_finite: "(map_option (Next \<circ> pre) \<circ> (fmlookup m)) \<in> {m. finite (dom m)}"
  by auto

text \<open>World satisfaction, i.e. the invariant that holds all invariants\<close>
definition wsat :: iprop where
  "wsat \<equiv> \<exists>\<^sub>u (I::(name,iprop) fmap).
    ((Own\<^sub>i(map_view_auth (DfracOwn 1) (lift_inv_fmap I),\<epsilon>,\<epsilon>))
    \<^emph> (sep_map_fmdom (\<lambda>\<iota>. (\<triangleright>(the (fmlookup I \<iota>))) \<^emph> ownD {|\<iota>|} \<or>\<^sub>u (ownE {\<iota>})) I)
  )"

lemma pcore_id_inv: "pcore_id_pred (constr_inv (map_view_frag \<iota> DfracDiscarded (Next (pre P)), \<epsilon>, \<epsilon>))"
  unfolding constr_inv_def prod_pcore_id_pred
  by (simp add: \<epsilon>_pcore_id_def) (rule pcore_id_frag[OF discarded_core_id])

lemma persistent_ownI [pers_rule]: "persistent (ownI \<iota> P)"
  unfolding ownI_def own_inv_def by (rule persistent_core_own2[OF pcore_id_inv])

lemma persistent_inv_raw [pers_rule]: "persistent (inv_raw N P)"
  unfolding inv_raw_def
  apply (rule persistent_exists)
  apply (rule persistent_conj)
  apply (rule persistent_pure)
  by (rule persistent_ownI)

lemma constr_inv_valid: "\<lbrakk>valid mv; valid e; valid d\<rbrakk> \<Longrightarrow> valid (constr_inv (mv,e,d))"
  unfolding constr_inv_def by (auto simp: prod_valid_def \<epsilon>_valid)

lemma ownE_singleton_twice: "ownE {i} \<^emph> ownE {i} \<turnstile> \<upharpoonleft>False"
  unfolding ownE_def own_inv_def constr_inv_def
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF own_op]])
  apply (rule upred_entails_trans[OF own_valid])
  apply (simp add: op_prod_def \<epsilon>_left_id op_dset_def)
  apply transfer
  by (simp add: prod_n_valid_def \<epsilon>_n_valid valid_raw_dset_def)

lemma ownD_singleton_twice: "ownD {|i|} \<^emph> ownD {|i|} \<turnstile> \<upharpoonleft>False"
  unfolding ownD_def own_inv_def constr_inv_def
  apply (auto simp: op_prod_def \<epsilon>_left_id op_dfset_def
    intro!: upred_entails_trans[OF upred_entail_eqR[OF own_op]] upred_entails_trans[OF own_valid])
  apply transfer
  by (simp add: prod_n_valid_def \<epsilon>_n_valid valid_raw_dfset_def)
  
lemma ownE_op: "E1 \<inter> E2 = {} \<Longrightarrow> ownE (E1 \<union> E2) \<stileturn>\<turnstile> ownE E1 \<^emph> ownE E2"
proof -
  assume "E1 \<inter> E2 = {}"
  then have un_op:"DSet (E1 \<union> E2) = DSet E1 \<cdot> DSet E2" unfolding op_dset_def by simp
  from own_op[of "constr_inv (\<epsilon>,DSet E1,\<epsilon>)" "constr_inv (\<epsilon>,DSet E2,\<epsilon>)"]
  show ?thesis by (auto simp: ownE_def own_inv_def un_op constr_inv_def op_prod_def \<epsilon>_left_id)
qed

lemma ownE_op_minus: "E1 \<subseteq> E2 \<Longrightarrow> ownE (E1 \<union> (E2-E1)) \<stileturn>\<turnstile> ownE E1 \<^emph> ownE (E2-E1)"
proof -
  assume "E1 \<subseteq> E2"
  then have "E1 \<inter> (E2-E1) = {}" by simp
  from ownE_op[OF this] show ?thesis .
qed
  
lemma auth_map_both_validI: 
  "\<V>(constr_inv (map_view_auth (DfracOwn 1) m,\<epsilon>,\<epsilon>) \<cdot> constr_inv (map_view_frag k dq v,\<epsilon>,\<epsilon>)) \<turnstile>
    (fmlookup m k =\<^sub>u Some v) \<and>\<^sub>u \<upharpoonleft>(valid dq)"
unfolding constr_inv_def op_prod_def
apply (simp add: \<epsilon>_left_id auth_comb_opL split: prod.splits)
apply transfer'
apply (simp add: prod_n_valid_def \<epsilon>_n_valid valid_raw_option_def \<epsilon>_option_def)
using map_view_both_valid by fastforce

lemma invariant_lookup: 
  "Own\<^sub>i (map_view_auth (DfracOwn 1) (lift_inv_fmap I),\<epsilon>,\<epsilon>) \<^emph> ownI \<iota> P \<turnstile> 
  (\<exists>\<^sub>u Q. \<upharpoonleft>(fmlookup I \<iota> = Some Q) \<^emph> \<triangleright>(Q=\<^sub>uP))"
  unfolding ownI_def own_inv_def
  apply (rule upred_entails_trans[OF upred_entail_eqR[OF own_op]])
  apply (rule upred_entails_trans[OF own_valid])
  apply (rule upred_entails_trans[OF auth_map_both_validI])
  apply transfer'
  apply (auto simp: lift_inv_fmap_def valid_raw_dfrac_def valid_def n_equiv_option_def 
    n_equiv_later_def Abs_fmap_inverse[OF lift_inf_fmap_finite])
  apply (metis dual_order.refl n_incl_def ofe_refl prod_cases3 total_n_inclI)
  by (metis \<epsilon>_left_id ofe_refl prod_cases3) 

lemma lookup_pers [pers_rule]: "persistent (\<exists>\<^sub>u Q. \<upharpoonleft>(fmlookup I \<iota> = Some Q) \<^emph> \<triangleright>(Q=\<^sub>uP))"
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
apply (rule add_holds[OF own_unit,unfolded bupd_emp[OF upred_own_nothing_emp_eq]])
apply (rule upred_entails_substE[OF upred_wand_holdsE[OF own_updateP]])
sorry (* Axiomatized as this requires too much low level ghost state reasoning for which I'd need to add
    way more lemmata and things. *)

lemma ownI_alloc_open: "(\<forall>E::name fset. \<exists>i. \<not>i|\<in>|E \<and> \<phi> i) \<Longrightarrow> 
  wsat ==\<^emph> (\<exists>\<^sub>u i. \<upharpoonleft>(\<phi> i) \<^emph> (ownE {i} -\<^emph> wsat) \<^emph> ownI i P \<^emph> ownD {|i|})"
apply (auto simp: wsat_def pull_exists_eq intro!: upred_wand_holdsI upred_existsE')
sorry (* Axiomatized as this requires too much low level ghost state reasoning for which I'd need to add
    way more lemmata and things. *)

lemma wsat_alloc: "\<Rrightarrow>\<^sub>b (\<exists>\<^sub>u _::inv. wsat \<^emph> ownE UNIV)"
apply (auto simp: upred_holds_entails)
apply (rule add_own[of "constr_inv (map_view_auth (DfracOwn 1) fmempty,\<epsilon>,\<epsilon>)", 
  OF constr_inv_valid[OF map_view_auth_valid \<epsilon>_valid \<epsilon>_valid]])
apply (rule add_own[of "constr_inv (\<epsilon>,DSet UNIV,\<epsilon>)", 
  OF constr_inv_valid[OF \<epsilon>_valid _ \<epsilon>_valid]])
apply (simp add: valid_raw_dset_def valid_def)
apply (rule add_own[of "constr_inv (\<epsilon>,\<epsilon>,DFSet {||})", 
  OF constr_inv_valid[OF \<epsilon>_valid \<epsilon>_valid _], unfolded \<epsilon>_dfset_def[symmetric], OF \<epsilon>_valid])
apply (auto simp: wsat_def pull_exists_eq own_inv_def ownE_def ownD_def 
  intro!: upred_entails_trans[OF _ updI])
apply (rule upred_existsI)
apply (rule upred_existsI[of _ _ fmempty])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
apply (auto intro!: upred_frame)
apply (auto simp: lift_inv_fmap_def fmempty.rep_eq fmempty_def[symmetric] sep_fold_fset_def 
  comp_fun_commute.ffold_empty[OF sep_P_comp_fun_commute]  intro!: upred_frame)
apply (rule upred_entails_trans[OF upred_entails_eq[OF upred_sep_comm2L]])
apply (rule upred_entails_trans[OF upred_sep_comm2R])
by (auto simp: upred_weakeningL intro!: upred_frame)

end