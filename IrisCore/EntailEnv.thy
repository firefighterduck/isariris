theory EntailEnv
imports Misc
begin

subsubsection \<open>An environment for entailments\<close>
text \<open>
  This environment is meant to make purely syntactical reasoning obsolete.
  It is loosely based on the env type from the Iris Proof Mode.
\<close>

declare [[typedef_overloaded = true]]
datatype entail_env = Env (pure: "bool fset") (pers: "iprop list") (spatial: "iprop list")

instantiation entail_env :: plus begin
definition plus_entail_env :: "entail_env \<Rightarrow> entail_env \<Rightarrow> entail_env" where
  "plus_entail_env e1 e2 = 
    Env (pure e1 |\<union>| pure e2) (pers e1 @ pers e2) (spatial e1 @ spatial e2)"
instance ..
end

definition env_iprop :: "entail_env \<Rightarrow> iprop" where
  "env_iprop env = sep_fold_list (sep_fold_list ([\<^emph>\<^sub>m] upred_pure (pure env)) (pers env)) (spatial env)"
  
lemma sep_list_singleton: "P \<equiv> [\<^emph>\<^sub>l] [P]" by (auto simp: upred_true_sep upred_sep_comm)

lemma sep_list_ind: "P \<equiv> [\<^emph>\<^sub>l] P' \<Longrightarrow> P\<^emph>Q \<equiv> [\<^emph>\<^sub>l] (P'@[Q])"
  by auto

lemma sep_list_dual: "P\<^emph>Q \<equiv> [\<^emph>\<^sub>l Q] [P]"
  by (auto simp: upred_sep_comm)

lemma sep_list_step: "[\<^emph>\<^sub>l Q] ((P\<^emph>R)#Seps) \<equiv> [\<^emph>\<^sub>l Q] (P#R#Seps)"
  by simp (smt (verit, ccfv_SIG) upred_sep_comm upred_sep_comm2_eq)

lemma sep_list_acc:"[\<^emph>\<^sub>l P\<^emph>Q] Seps = P \<^emph> [\<^emph>\<^sub>l Q] Seps"
  by (induction Seps arbitrary: Q) (simp_all add: upred_sep_assoc_eq)

lemma sep_list_cons: "[\<^emph>\<^sub>l P] (Q#Seps) = Q \<^emph> [\<^emph>\<^sub>l P] Seps"
  by (metis (no_types, lifting) foldl_Cons  sep_list_acc upred_sep_comm)
  
lemma envI: "[\<^emph>\<^sub>l] P \<equiv> ([\<^emph>\<^sub>l] P) \<^emph> (env_iprop (Env {||} [] []))"
  by (simp add: env_iprop_def sep_fold_fset_def 
    comp_fun_commute.ffold_empty[OF sep_comp_fun_commute] upred_true_sep)

lemma pure_insert_idem: "b |\<in>| pure e \<Longrightarrow> env_iprop (Env (finsert b (pure e)) (pers e) (spatial e))
  \<equiv> env_iprop e"
  by (simp add: env_iprop_def sep_fold_fset_def finsert_absorb)

lemma move_pure_env: "([\<^emph>\<^sub>l] ((\<upharpoonleft>b)#P)) \<^emph> (env_iprop (Env pu pe sp)) \<equiv> 
  ([\<^emph>\<^sub>l] P) \<^emph> (env_iprop (Env (finsert b pu) pe sp))" (is "?l \<equiv> ?r")
proof -
have "?l = ([\<^emph>\<^sub>l] P) \<^emph> \<upharpoonleft>b \<^emph> (env_iprop (Env pu pe sp))"
  using sep_list_cons by (simp add: upred_sep_comm)
then have "?l = ([\<^emph>\<^sub>l] P) \<^emph> \<upharpoonleft>b \<^emph> [\<^emph>\<^sub>l [\<^emph>\<^sub>l [\<^emph>\<^sub>m] upred_pure pu] pe] sp"
  unfolding env_iprop_def by simp  
then have "?l = ([\<^emph>\<^sub>l] P) \<^emph> (foldl (\<^emph>) (foldl (\<^emph>) (ffold (\<lambda>x a. a \<^emph> \<upharpoonleft>x) 
  upred_emp pu) pe) sp) \<^emph> \<upharpoonleft>b"
  apply (simp add: sep_fold_fset_def)
  using upred_sep_assoc_eq upred_sep_comm2_eq by (smt (verit, del_insts))
then have "?l = ([\<^emph>\<^sub>l] P) \<^emph> foldl (\<^emph>) (foldl (\<^emph>) (ffold (\<lambda>x a. a \<^emph> \<upharpoonleft>x) 
  upred_emp pu) pe \<^emph> \<upharpoonleft>b) sp"
  apply (simp add: sep_list_acc upred_sep_comm)
  by (metis (no_types, lifting) upred_sep_assoc_eq upred_sep_comm)
then have innermost_eq: "?l = ([\<^emph>\<^sub>l] P) \<^emph> foldl (\<^emph>) (foldl (\<^emph>) (ffold (\<lambda>x a. a \<^emph> \<upharpoonleft>x) 
  upred_emp pu \<^emph> \<upharpoonleft>b) pe) sp"
  by (simp add: sep_list_acc upred_sep_comm)
have "?l = ?r" proof (cases "b |\<in>| pu")
    case True
    have "ffold (\<lambda>x a. a \<^emph> \<upharpoonleft>x) upred_emp pu \<^emph> (\<upharpoonleft>b) = 
      ffold (\<lambda>x a. a \<^emph> \<upharpoonleft>x) upred_emp (pu |-| {|b|}) \<^emph> \<upharpoonleft>b \<^emph> \<upharpoonleft>b" (is "?l1 = _")
      using comp_fun_commute.ffold_rec[OF sep_P_comp_fun_commute[of upred_pure] True] by metis
    then have "?l1 = ffold (\<lambda>x a. a \<^emph> \<upharpoonleft>x) upred_emp (pu |-| {|b|}) \<^emph> \<upharpoonleft>b"
      using pure_dupl by (smt (verit, ccfv_SIG) upred_sep_assoc_eq)
    then have "?l1 = ffold (\<lambda>x a. a \<^emph> \<upharpoonleft>x) upred_emp pu" 
      using comp_fun_commute.ffold_rec[OF sep_P_comp_fun_commute[of upred_pure] True] by metis
    then have ff_pure_eq: "?l1 = ffold (\<lambda>x a. a \<^emph> \<upharpoonleft>x) upred_emp (finsert b pu)"
      using finsert_absorb[OF True] by simp
    show ?thesis unfolding innermost_eq
    unfolding sep_fold_fset_def env_iprop_def
    apply simp unfolding ff_pure_eq ..   
  next
    case False
    show ?thesis unfolding innermost_eq 
    unfolding env_iprop_def sep_fold_fset_def
    unfolding comp_fun_commute.ffold_finsert[OF sep_P_comp_fun_commute[of upred_pure] False, symmetric]
    by simp
  qed
then show "?l \<equiv> ?r" by simp
qed
   
lemma move_pers_env: 
  "([\<^emph>\<^sub>l] (Q#P)) \<^emph> (env_iprop (Env pu pe sp)) \<equiv> ([\<^emph>\<^sub>l] P) \<^emph> (env_iprop (Env pu (Q#pe) sp))"
  unfolding sep_list_cons by (simp add: env_iprop_def sep_fold_fset_def)
    (smt (verit) sep_list_acc upred_sep_comm upred_sep_comm2_eq)

lemma move_spatial_env: 
  "([\<^emph>\<^sub>l] (Q#P)) \<^emph> (env_iprop (Env pu pe sp)) \<equiv> ([\<^emph>\<^sub>l] P) \<^emph> (env_iprop (Env pu pe (Q#sp)))"
  unfolding sep_list_cons by (simp add: env_iprop_def sep_fold_fset_def)
    (smt (verit) sep_list_acc upred_sep_comm upred_sep_comm2_eq)
 
ML \<open>
  val sep_list_conv = Conv.rewr_conv @{thm sep_list_singleton}
    then_conv Conv.repeat_changed_conv (Conv.rewr_conv @{thm sep_list_step})
  val list_env_conv = Conv.rewr_conv @{thm envI} then_conv Conv.repeat_changed_conv (
    Conv.rewr_conv @{thm move_pure_env} else_conv (* Conv.rewr_conv @{thm move_pers_env} else_conv *) 
    Conv.rewr_conv @{thm move_spatial_env})
  fun params_conv ctxt cv ct = 
    if Logic.is_all (Thm.term_of ct)
    then Conv.arg_conv (Conv.abs_conv (fn (_, ctxt) => params_conv ctxt cv) ctxt) ct
    else cv ct;
  fun env_conv ctxt = sep_list_conv then_conv list_env_conv 
    |> Conv.binop_conv 
    |> HOLogic.Trueprop_conv
    |> params_conv ctxt
  fun sep_list_tac ctxt = CONVERSION (env_conv ctxt)

  val test = \<^cterm>\<open>\<And>x y z. (\<upharpoonleft>x) \<^emph> y \<^emph> z \<turnstile> y \<^emph> w \<^emph> (z::iprop)\<close>
  val test_result = env_conv \<^context> test
\<close>

end