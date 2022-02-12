theory EntailEnv
imports Misc 
begin

subsubsection \<open>An environment for entailments\<close>
text \<open>
  This environment is meant to make purely syntactical reasoning obsolete.
  It is loosely based on the env type from the Iris Proof Mode.
\<close>

declare [[typedef_overloaded = true]]
datatype entail_env = Env (pers: "iprop fset") (spatial: "iprop list") (* maybe multiset?*)

instantiation entail_env :: plus begin
definition plus_entail_env :: "entail_env \<Rightarrow> entail_env \<Rightarrow> entail_env" where
  "plus_entail_env e1 e2 = 
    Env (pers e1 |\<union>| pers e2) (spatial e1 @ spatial e2)"
instance ..
end

definition env_iprop :: "entail_env \<Rightarrow> iprop" where
  "env_iprop env = [\<^emph>\<^sub>l [\<^emph>\<^sub>m] id (pers env)] (spatial env)"
  
lemma sep_list_singleton: "P \<equiv> [\<^emph>\<^sub>l] [P]" by (auto simp: upred_true_sep upred_sep_comm)

lemma sep_list_acc:"[\<^emph>\<^sub>l P\<^emph>Q] Seps = P \<^emph> [\<^emph>\<^sub>l Q] Seps"
  by (induction Seps arbitrary: Q) (simp_all add: upred_sep_assoc_eq)

lemma sep_list_cons: "[\<^emph>\<^sub>l P] (Q#Seps) = Q \<^emph> [\<^emph>\<^sub>l P] Seps"
  by (metis (no_types, lifting) foldl_Cons sep_list_acc upred_sep_comm)

lemma sep_list_step: "[\<^emph>\<^sub>l Q] ((P\<^emph>R)#Seps) \<equiv> [\<^emph>\<^sub>l Q] (P#R#Seps)"
  by (smt (verit, del_insts) foldl_Nil foldl_append sep_list_cons upred_sep_assoc_eq)

lemma sep_listI: "P \<equiv> P \<^emph> [\<^emph>\<^sub>l] []"
  by (simp add: upred_true_sep)
lemma sep_list_ind: "P \<^emph> Q \<^emph> [\<^emph>\<^sub>l] L \<equiv> P \<^emph> [\<^emph>\<^sub>l] (Q#L)"
  using sep_list_cons sep_list_step by presburger
lemma sep_list_drop: "P \<^emph> [\<^emph>\<^sub>l] L \<equiv> [\<^emph>\<^sub>l] (P#L)"
  using sep_list_cons by auto

lemma envI: "[\<^emph>\<^sub>l] P \<equiv> [\<^emph>\<^sub>l] P \<^emph> (env_iprop (Env {||} []))"
  by (simp add: env_iprop_def sep_fold_fset_def comp_fun_commute.ffold_empty[OF sep_comp_fun_commute]
    upred_true_sep)

lemma sep_listE: "[\<^emph>\<^sub>l] [] \<^emph> env_iprop e \<equiv> env_iprop e"  
  by (smt (verit) foldl_Nil upred_sep_comm upred_true_sep)

lemma move_pure: "(b \<Longrightarrow> [\<^emph>\<^sub>l] Seps \<^emph> (env_iprop e) \<turnstile> Q) \<Longrightarrow> [\<^emph>\<^sub>l] (\<upharpoonleft>b)#Seps \<^emph> (env_iprop e) \<turnstile> Q"
  by (metis (full_types) false_entails false_sep sep_list_cons upred_sep_comm upred_true_sep)

lemma move_spatial_env: 
  "([\<^emph>\<^sub>l] (Q#P)) \<^emph> (env_iprop (Env pe sp)) \<equiv> ([\<^emph>\<^sub>l] P) \<^emph> (env_iprop (Env pe (Q#sp)))"
  unfolding sep_list_cons by (simp add: env_iprop_def sep_fold_fset_def)
    (smt (verit) sep_list_acc upred_sep_comm upred_sep_comm2_eq)

lemma move_pers_env: "persistent Q \<Longrightarrow>
  env_iprop (Env pe (Q#sp)) \<turnstile> env_iprop (Env (finsert Q pe) sp)"
  unfolding env_iprop_def sep_fold_fset_def
  apply (cases "Q |\<in>| pe")
  apply (simp_all add: finsert_absorb upred_frame upred_weakeningR sep_list_acc upred_sep_comm)
  using comp_fun_commute.ffold_finsert[OF sep_P_comp_fun_commute[of id], simplified]
  by (simp add: comp_fun_commute.ffold_finsert sep_comp_fun_commute sep_list_acc)

lemma flip_spatial: "env_iprop (Env pe (Q#sp)) \<equiv> env_iprop (Env pe (sp@[Q]))"
  by (simp add: sep_list_acc upred_sep_comm env_iprop_def)

lemma env_exchange: 
assumes "P\<^emph>Q\<turnstile>R" "persistent P" "P|\<in>|pe" "env_iprop (Env pe (R#sp))\<turnstile>T"
shows "env_iprop (Env pe (Q#sp))\<turnstile>T"
proof -
  from assms(4) have "env_iprop (Env pe sp) \<^emph> R\<turnstile>T" 
    by (simp add: sep_list_acc upred_sep_comm env_iprop_def sep_list_cons)  
  from upred_entails_exchange[OF assms(1) this] have "env_iprop (Env pe sp) \<^emph> (P \<^emph> Q) \<turnstile> T" .
  then have "env_iprop (Env pe sp) \<^emph> P \<^emph> Q \<turnstile> T" using upred_sep_assoc_eq by (metis (no_types, lifting))
  with assms(3) have "env_iprop (Env (pe |-| {|P|}) sp) \<^emph> P \<^emph> P \<^emph> Q \<turnstile> T"
    apply (simp add: env_iprop_def sep_fold_fset_def)
    using comp_fun_commute.ffold_rec[OF sep_P_comp_fun_commute[of id] assms(3), simplified]
    by (simp add: sep_list_acc upred_sep_comm)
  then have "env_iprop (Env (pe |-| {|P|}) sp) \<^emph> Q \<^emph> (P \<^emph> P)  \<turnstile> T"
    by (simp add: upred_sep_comm2L upred_sep_comm2_eq)
  from upred_entails_exchange[OF upred_entail_eqR[OF persistent_dupl[OF assms(2)]] this]
  have "env_iprop (Env (pe |-| {|P|}) sp) \<^emph> P \<^emph> Q \<turnstile> T"
    by (simp add: upred_sep_comm2_eq)
  then have "env_iprop (Env pe sp) \<^emph> Q \<turnstile> T" 
    apply (simp add: env_iprop_def sep_fold_fset_def)
    using comp_fun_commute.ffold_rec[OF sep_P_comp_fun_commute[of id] assms(3), simplified, symmetric]
    by (metis (no_types, lifting) sep_list_acc upred_sep_comm)
  then show ?thesis
    by (simp add: env_iprop_def sep_fold_fset_def sep_list_acc upred_sep_comm)
qed

lemma do_proof_step_with_env:
assumes "P\<turnstile>Q" "P = [\<^emph>\<^sub>l] P'" "\<forall>p \<in># (mset P'). (persistent p \<and> p |\<in>| pe) \<or> p \<in># (mset sp)" 
  "Q = [\<^emph>\<^sub>l] Q'" "env_iprop (Env pe (Q'@sp)) \<turnstile> R"
shows "env_iprop (Env pe sp) \<turnstile> R"
sorry

ML \<open>
  val sep_list_conv = Conv.rewr_conv @{thm sep_list_singleton}
    then_conv Conv.repeat_changed_conv (Conv.rewr_conv @{thm sep_list_step})
  fun embed_conv ctxt cv = (cv 
    |> Conv.arg_conv (* Only transform the antecedent *)
    |> Conv.fun_conv (* Go below the "\<turnstile>" *)
    |> HOLogic.Trueprop_conv
    |> Conv.concl_conv ~1 (* Go below any assumptions *)
    |> (fn cv => Conv.params_conv ~1 (K cv) ctxt))
    handle CTERM _ => Conv.all_conv
  fun env_conv ctxt = embed_conv ctxt (sep_list_conv then_conv Conv.rewr_conv @{thm envI})
  fun move_to_env_conv ctxt = embed_conv ctxt (Conv.rewr_conv @{thm move_spatial_env})
  fun drop_list_conv ctxt = embed_conv ctxt (Conv.rewr_conv @{thm sep_listE})
  fun flip_spat_conv ctxt = embed_conv ctxt (Conv.rewr_conv @{thm flip_spatial})
  
  val reduce_list_conv_raw = Conv.rewr_conv @{thm sep_listI}
    then_conv Conv.repeat_changed_conv (Conv.rewr_conv @{thm sep_list_ind})
    then_conv (Conv.rewr_conv @{thm sep_list_drop})
  fun reduce_list_conv ctxt = embed_conv ctxt reduce_list_conv_raw

  fun sep_env_tac ctxt = FIRSTGOAL (
    CONVERSION (env_conv ctxt) (* First introduce the list and emtpy env*)
    THEN' (fn i => REPEAT_DETERM (CHANGED ((resolve_tac ctxt [@{thm move_pure}] ORELSE'
      CONVERSION (move_to_env_conv ctxt)) i))) (* Then move all pure into context and rest into env*)
    THEN' CONVERSION (drop_list_conv ctxt) (* Now drop the empty list *)
  )

  val persN = "pers_rules"
  fun get_pers_thms lthy  = Proof_Context.get_thms lthy (Long_Name.qualify persN persN)
  fun pers_tac ctxt = (fn i => (CHANGED (resolve_tac ctxt (get_pers_thms ctxt) i)))
    |> REPEAT_ALL_NEW |> SOLVED'
  fun strip_impl (Const (\<^const_name>\<open>Pure.imp\<close>,_) $ _ $ b) = strip_impl b
    | strip_impl t = t
  fun get_spatial_number thm = (if Thm.nprems_of thm > 0 then
    Thm.cprem_of thm 1 |> Thm.term_of
    |> strip_all_body
    |> strip_impl
    |> dest_comb |> snd (* Strip Trueprop*)
    |> strip_comb |> snd |> hd (* Strip entails*)
    |> dest_comb |> snd (* Strip env_iprop *)
    |> dest_comb |> snd (*Strip Env Constructor *)
    |> HOLogic.dest_list |> length
    else 0) handle THM _ => 0 | CTERM _ => 0 | TERM _ => 0
  fun is_pers_tac ctxt i thm = let val rounds = get_spatial_number thm in
    REPEAT_DETERM_N rounds
     ((resolve_tac ctxt @{thms upred_entails_trans[OF move_pers_env]} i
       THEN HEADGOAL (pers_tac ctxt))
     ORELSE ((CONVERSION (flip_spat_conv ctxt) THEN' simp_tac ctxt) i)) thm end

  fun env_tac ctxt = sep_env_tac ctxt THEN (is_pers_tac ctxt 1)
\<close>

axiomatization w :: iprop
lemma pers_w [pers_rule]: "persistent w" sorry

lemma "\<And>x y z. (\<upharpoonleft>x) \<^emph> z \<^emph> w \<^emph> y \<turnstile> y \<^emph> w \<^emph> (z::iprop)"
apply (tactic \<open>env_tac \<^context>\<close>)
sorry
end