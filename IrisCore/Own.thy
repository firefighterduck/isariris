theory Own
imports ProofRules
begin

context inG begin
definition own :: "gname \<Rightarrow> 'b \<Rightarrow> 'a upred_f" where
  "own \<gamma> x = upred_own (put_cmra \<gamma> x)"

lemma own_ne [upred_ne_rule]: "n_equiv n x y \<Longrightarrow> n_equiv n (own \<gamma> x) (own \<gamma> y)" 
  unfolding own_def
  apply (rule upred_own_ne)
  using non_expansiveE[OF put_ne] by simp

lemma own_valid: "own \<gamma> a \<turnstile> \<V>(a)"
  unfolding own_def
  apply (rule upred_entails_trans[OF upred_own_valid])
  by (auto simp: upred_entails.rep_eq upred_valid.rep_eq put_n_valid)

lemma own_op: "own \<gamma> (a\<cdot>b) \<stileturn>\<turnstile> own \<gamma> a \<^emph> own \<gamma> b"
  unfolding own_def put_op
  by (rule upred_own_op)

lemma own_valid2: "own \<gamma> a1 -\<^emph> own \<gamma> a2 -\<^emph> \<V>(a1\<cdot>a2)"
  unfolding own_def
  apply (rule upred_wand_holds2I)
  apply (rule upred_entails_trans[OF upred_wand_holds2E[OF upred_own_valid2]])
  by (auto simp: upred_entails.rep_eq upred_valid.rep_eq put_n_valid put_op[symmetric])

lemma own_alloc: "valid a \<Longrightarrow> \<Rrightarrow>\<^sub>b (own \<gamma> a)"
  sorry (* Axiomatized as proof in Coq is not easily reproducible. *)
  
lemma own_update: "put_cmra \<gamma> a\<leadsto>{put_cmra \<gamma> b} \<Longrightarrow> own \<gamma> a ==\<^emph> own \<gamma> b"
  unfolding camera_upd_def own_def
  apply (rule upred_wand_holdsI)
  apply transfer'
  apply auto
  by (metis n_incl_refl n_valid_incl_subst)

lemma add_own: "\<lbrakk>valid a; Q\<^emph>(own \<gamma> a)\<turnstile>\<Rrightarrow>\<^sub>bR\<rbrakk> \<Longrightarrow> Q\<turnstile>\<Rrightarrow>\<^sub>bR"
proof -
  assume assms: "valid a" "Q\<^emph>(own \<gamma> a)\<turnstile>\<Rrightarrow>\<^sub>bR"
  from own_alloc[OF this(1)] have "\<Rrightarrow>\<^sub>b own \<gamma> a" .
  from assms(2) have "Q\<^emph>\<Rrightarrow>\<^sub>b own \<gamma> a\<turnstile>\<Rrightarrow>\<^sub>b R"
    by (meson upd_frameR upd_mono upd_idem upred_entails_trans)
  from add_holds[OF \<open>\<Rrightarrow>\<^sub>b own \<gamma> a\<close> this] show ?thesis .
qed  
end

notation inG.own ("own _ _ _")

context fixes get_cmra :: "gname \<Rightarrow> 'a::ucamera \<Rightarrow> 'b::total_camera option"
  and put_cmra :: "gname \<Rightarrow> 'b \<Rightarrow> 'a"
  assumes inG: "inG get_cmra put_cmra"
begin
lemma own_core_persis: "own put_cmra \<gamma> a \<turnstile> \<box>(own put_cmra \<gamma> (core a))"
  unfolding inG.own_def[OF inG]
  apply (rule upred_entails_trans[OF upred_own_core_persis])
  unfolding core_def
  apply (auto simp: comp_def inG.put_pcore[OF inG])
  using total_pcore
  by (metis option.case_eq_if option.distinct(1) upred_entails_refl)

lemma pcore_id_put: "pcore_id_pred x \<Longrightarrow> pcore_id_pred (put_cmra \<gamma> x)"
  unfolding pcore_id_pred_def inG.put_pcore[OF inG]
  by auto
end
end