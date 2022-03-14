theory Automation
imports ProofSearchPredicates "HOL-Eisbach.Eisbach_Tools"
begin

method iIntro = 
  (match conclusion in "upred_holds _" \<Rightarrow> \<open>rule upred_wand_holdsI\<close>)?,((rule upred_wandI)+)?

method remove_emp = (simp_all only: upred_sep_assoc_eq emp_rule)?

method log_prog_solver =
  fast intro: log_prog_rule
| slow intro: log_prog_rule
| best intro: log_prog_rule
(*| force intro: log_prog_rule
| blast 5 intro: log_prog_rule*)

text \<open>A simple attribute to convert upred_holds predicates into entailments.\<close>
ML \<open> val to_entailment: attribute context_parser = let 
  fun is_upred_holds (Const(\<^const_name>\<open>Trueprop\<close>,_)$(Const(\<^const_name>\<open>upred_holds\<close>,_)$_)) = true
    | is_upred_holds _ = false
  fun match_upred_holds thm = is_upred_holds (Thm.concl_of thm)

  fun is_wand_term (Const(\<^const_name>\<open>upred_wand\<close>,_)$_$_) = true
    | is_wand_term _ = false

  fun contains_wand thm = Thm.concl_of thm
    |> dest_comb |> snd (* Strip Trueprop*)
    |> strip_comb |> snd |> tl |> hd (* Strip entails*)
    |> is_wand_term

  fun contains_emp (Const(\<^const_name>\<open>upred_pure\<close>,_)$Const(\<^const_name>\<open>True\<close>,_)) = true
    | contains_emp (f$x) = contains_emp f orelse contains_emp x
    | contains_emp _ = false

  fun remove_emp thm = if contains_emp (Thm.concl_of thm
      |> dest_comb |> snd (* Strip Trueprop*)
      |> strip_comb |> snd |> hd (* Strip entails*))
    then Conv.fconv_rule (Conv.rewr_conv @{thm  eq_reflection[OF upred_sep_comm]}
      then_conv (Conv.rewr_conv @{thm  eq_reflection[OF upred_true_sep]})
      |> Conv.arg_conv (* Only transform the antecedent *)
      |> Conv.fun_conv (* Go below the "\<turnstile>" *) 
      |> HOLogic.Trueprop_conv
      |> Conv.concl_conv ~1)
      thm
    else thm

  fun to_entail thm = (if match_upred_holds thm 
    then Conv.fconv_rule (Conv.rewr_conv @{thm eq_reflection[OF upred_holds_entails]}
      |> HOLogic.Trueprop_conv
      |> Conv.concl_conv ~1)
      thm
    else thm)

  fun move_wands thm = (if contains_wand thm then (@{thm upred_wandE} OF [thm]) |> remove_emp |> move_wands
    else thm)
  in
    (fn whatevs => ((fn (ctxt, thm) => let val thm' = try (move_wands o to_entail) thm in
    (SOME ctxt, thm')end), whatevs)) end
\<close>
attribute_setup to_entailment = \<open>to_entailment\<close>

text \<open>Find a subgoal on which the given method is applicable, prefer that subgoal and apply the method.
  This will result in new subgoals to be at the head. Requires to evaluate the method for all subgoals
  up to the applicable goal and another time for that goal.\<close>
method_setup apply_prefer =
  \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>  
    let fun prefer_first i thm = 
      let val applicable = case Seq.pull (SELECT_GOAL (method_evaluate m ctxt facts) i thm) 
        of SOME _ => true
        | NONE => false
      in (if applicable then prefer_tac i thm else no_tac thm) end
    in SIMPLE_METHOD ((FIRSTGOAL prefer_first) THEN (method_evaluate m ctxt facts)) facts end)\<close>

text \<open>Find a subgoal on which the given method is applicable and apply the method there.
  This will not move any subgoals around and resulting subgoals will not be at the head. 
  Requires the method to be evaluated for all subgoals at most once.\<close>
method_setup apply_first =
  \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>  
    let fun eval_method i = 
      SELECT_GOAL (method_evaluate m ctxt facts) i
    in SIMPLE_METHOD (FIRSTGOAL eval_method) facts end)\<close>

method entails_substL uses rule =
  match rule[uncurry] in "_ = _" \<Rightarrow> \<open>rule upred_entails_trans[OF upred_entails_eq[OF rule]]\<close>
  \<bar> "_ \<Longrightarrow> (_=_)" \<Rightarrow> \<open>rule upred_entails_trans[OF upred_entails_eq[OF rule]]\<close>
  \<bar> "_\<turnstile>_" \<Rightarrow> \<open>rule rule
    | rule upred_entails_substE[OF rule, unfolded upred_sep_assoc_eq]
    | rule upred_entails_trans[OF rule] | rule upred_entails_substE'[OF rule, unfolded upred_conj_assoc]\<close>
  \<bar> "_ \<Longrightarrow> (_ \<turnstile> _)" \<Rightarrow> \<open>rule rule
    | rule upred_entails_substE[OF rule, unfolded upred_sep_assoc_eq]
    | rule upred_entails_trans[OF rule] | rule upred_entails_substE'[OF rule, unfolded upred_conj_assoc]\<close>
  \<bar> R[curry]: "upred_holds _" \<Rightarrow> \<open>entails_substL rule: R[to_entailment]\<close>
  \<bar> R[curry]: "_ \<Longrightarrow> upred_holds _" \<Rightarrow> \<open>entails_substL rule: R[to_entailment]\<close>
  
method entails_substR uses rule = 
  match rule[uncurry] in "_ = _" \<Rightarrow> \<open>rule upred_entails_trans[OF _ upred_entails_eq[OF rule]]\<close>
  \<bar> "_ \<Longrightarrow> (_=_)" \<Rightarrow> \<open>rule upred_entails_trans[OF _ upred_entails_eq[OF rule]]\<close>
  \<bar> "_\<turnstile>_" \<Rightarrow> \<open>rule rule
    | rule upred_entails_substI[OF rule, unfolded upred_sep_assoc_eq]
    | (rule upred_entails_trans[OF _ rule])\<close>
  \<bar> "_ \<Longrightarrow> (_ \<turnstile> _)" \<Rightarrow> \<open>rule rule
    | rule upred_entails_substI[OF rule, unfolded upred_sep_assoc_eq]
    | rule upred_entails_trans[OF _ rule]\<close>
  \<bar> R[curry]: "upred_holds _" \<Rightarrow> \<open>entails_substR rule: R[to_entailment]\<close>
  \<bar> R[curry]: "_ \<Longrightarrow> upred_holds _" \<Rightarrow> \<open>entails_substR rule: R[to_entailment]\<close>
  
method dupl_pers = (entails_substL rule: upred_entail_eqR[OF persistent_dupl], log_prog_solver)?
                                               
method subst_pers_keepL uses rule =
  (entails_substL rule: persistent_keep[OF _ rule], log_prog_solver)
| entails_substL rule: rule

text \<open>Unchecked move methods, might not terminate if pattern is not found.\<close>   
method move_sepL for pat :: "'a::ucamera upred_f" =
  match conclusion in \<open>hyps \<turnstile> _\<close> for hyps :: "'a upred_f" \<Rightarrow>
    \<open> match (hyps) in "pat" \<Rightarrow> succeed
      \<bar> "_\<^emph>pat" \<Rightarrow> succeed
      \<bar> "pat\<^emph>_" \<Rightarrow> \<open>subst upred_sep_comm\<close>
      \<bar> "_\<^emph>pat\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm2R\<close>
      \<bar> "pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm2L; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm3M; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm3L; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm4_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm4_1; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm5_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm5_1; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm6_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm6_1; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm7_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm7_1; move_sepL pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm8_2; move_sepL pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm8_1; move_sepL pat\<close>
      \<bar> "_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm8_1; move_sepL pat\<close>
    \<close>
    
method move_sepR for pat :: "'a::ucamera upred_f" =
  match conclusion in \<open>_ \<turnstile> goal\<close> for goal :: "'a upred_f" \<Rightarrow>
    \<open> match (goal) in "pat" \<Rightarrow> succeed
      \<bar> "_\<^emph>pat" \<Rightarrow> succeed
      \<bar> "pat\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm\<close>
      \<bar> "_\<^emph>pat\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm2R\<close>
      \<bar> "pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm2L; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm3M; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm3L; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm4_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm4_1; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm5_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm5_1; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm6_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm6_1; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm7_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm7_1; move_sepR pat\<close>
      \<bar> "_\<^emph>pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm8_2; move_sepR pat\<close>
      \<bar> "pat\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm8_1; move_sepR pat\<close>
      \<bar> "_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_\<^emph>_" \<Rightarrow> \<open>entails_substR rule: upred_sep_comm8_1; move_sepR pat\<close>
    \<close>

method move_sep for left :: bool and pat :: "'a::ucamera upred_f" = 
  match (left) in True \<Rightarrow> \<open>move_sepL pat\<close>
  \<bar> False \<Rightarrow> \<open>move_sepR pat\<close>
    
method move_sep_all for left :: bool and trm :: "'a::ucamera upred_f" =
  match (trm) in "rest\<^emph>head" for rest head :: "'a upred_f" \<Rightarrow> \<open>move_sep_all left rest; move_sep left head\<close>
  \<bar> "P" for P :: "'a upred_f" \<Rightarrow> \<open>move_sep left P\<close>

method move_sep_both for trm :: "'a::ucamera upred_f" =
  move_sepL trm, move_sepR trm

method move_sep_all_both for pat :: "'a::ucamera upred_f" =
  move_sep_all True pat, move_sep_all False pat
  
text \<open>Checked move methods, guaranteed to terminate.\<close>
method find_pat_sep for pat trm :: "'a::ucamera upred_f" = 
  match (trm) in "pat" \<Rightarrow> succeed
  \<bar> "_\<^emph>pat" \<Rightarrow> succeed
  \<bar> "pat\<^emph>_" \<Rightarrow> succeed
  \<bar> "rest\<^emph>_" for rest :: "'a upred_f" \<Rightarrow> \<open>find_pat_sep pat rest\<close>   

method find_in_pat_sep for pat trm :: "'a::ucamera upred_f" = 
  match (pat) in "rest\<^emph>head" for rest head :: "'a upred_f" \<Rightarrow>
    \<open> match (trm) in head \<Rightarrow> succeed | find_in_pat_sep rest trm \<close>
  \<bar> "single_pat" for single_pat \<Rightarrow> \<open> match (trm) in single_pat \<Rightarrow> succeed \<close>

method find_other_than_pat_sep for pat trm :: "'a::ucamera upred_f" =
  match (trm) in "pat" \<Rightarrow> fail
  \<bar> "rest\<^emph>pat" for rest :: "'a upred_f" \<Rightarrow> \<open>find_other_than_pat_sep pat rest\<close>
  \<bar> "_" \<Rightarrow> succeed  
  
method check_not_headL for pat :: "'a::ucamera upred_f" =
  match conclusion in "_\<^emph>head\<turnstile>_" for head :: "'a upred_f" \<Rightarrow> \<open>find_other_than_pat_sep pat head\<close>

method check_moveL for pat :: "'a::ucamera upred_f" =
  match conclusion in \<open>hyps \<turnstile> _\<close> for hyps :: "'a upred_f" \<Rightarrow>
    \<open> find_pat_sep pat hyps; move_sepL pat\<close>
    
method check_moveR for pat :: "'a::ucamera upred_f" =
  match conclusion in \<open>_ \<turnstile> goal\<close> for goal :: "'a upred_f" \<Rightarrow>
    \<open> find_pat_sep pat goal; move_sepR pat\<close>
    
method check_move for left :: bool and pat :: "'a::ucamera upred_f" = 
  match (left) in True \<Rightarrow> \<open>check_moveL pat\<close>
  \<bar> False \<Rightarrow> \<open>check_moveR pat\<close>  

method check_move_all for left :: bool and trm :: "'a::ucamera upred_f" =
  match (trm) in "rest\<^emph>head" for rest head :: "'a upred_f" \<Rightarrow> 
    \<open>check_move_all left rest; check_move left head\<close>
  \<bar> "P" for P :: "'a upred_f" \<Rightarrow> \<open>check_move left P\<close>

method check_move_both for trm :: "'a::ucamera upred_f" =
  (check_moveL trm, dupl_pers), check_moveR trm
  
method check_move_dupl_all for left acc_pure :: bool and trm :: "'a::ucamera upred_f" =
  match (trm) in "rest\<^emph>\<upharpoonleft>head" for rest :: "'a upred_f" and head \<Rightarrow> \<open>match (acc_pure) in True \<Rightarrow> succeed 
    \<bar> False \<Rightarrow> \<open>check_move left "\<upharpoonleft>head", dupl_pers, check_move_dupl_all left acc_pure rest\<close>\<close>
  \<bar> "rest\<^emph>head" for rest head :: "'a upred_f" \<Rightarrow>
    \<open>check_move left head, dupl_pers, check_move_dupl_all left acc_pure rest\<close>
  \<bar> "P" for P :: "'a upred_f" \<Rightarrow> \<open>check_move left P, dupl_pers\<close>

method check_move_all_both for pat :: "'a::ucamera upred_f" =
  (check_move_dupl_all True False pat, move_sep_all True pat), check_move_all False pat
  
text \<open>Moves all hypotheses while duplicating all persistent, then moves again but unchecked to get 
  correct order of hypotheses. Then applies given rule.\<close>
method iApply uses rule =
  match rule[uncurry] in "hyps \<turnstile> _" for hyps \<Rightarrow> \<open>check_move_dupl_all True True hyps, move_sep_all True hyps, 
    subst_pers_keepL rule: rule\<close>
  \<bar> "_ \<Longrightarrow> hyps \<turnstile> _" for hyps \<Rightarrow> \<open>check_move_dupl_all True True hyps, move_sep_all True hyps,
    subst_pers_keepL rule: rule\<close>
  \<bar> R[curry]: "upred_holds _" \<Rightarrow> \<open>iApply rule: R[to_entailment]\<close>
  \<bar> R[curry]: "_ \<Longrightarrow> upred_holds _" \<Rightarrow> \<open>iApply rule: R[to_entailment]\<close>

text \<open>Looks for the head term in the given pattern and separates matches to the right.\<close>
method split_pat for pat :: "'a::ucamera upred_f" = repeat_new
  \<open>((match conclusion in "can_be_split (_\<^emph>_) _ _" \<Rightarrow> succeed),
  (((match conclusion in "can_be_split (_\<^emph>head) _ _" for head :: "'a upred_f" \<Rightarrow>
      \<open>find_in_pat_sep pat head\<close>), rule can_be_split_sepR)
    | rule can_be_split_sepL))
| ((match conclusion in "can_be_split (_\<or>\<^sub>u_) _ _" \<Rightarrow> succeed),rule can_be_split_disj)
| (((match conclusion in "can_be_split head _ _" for head :: "'a upred_f" \<Rightarrow>
      \<open>find_in_pat_sep pat head\<close>), rule can_be_split_baseR)
    | rule can_be_split_baseL)\<close>

text \<open>Separates the top terms (the same number as the patterns) to the right and the rest to the left.
  If it should separate the terms in the pattern, they first need to be moved to the top level.\<close>
method ord_split_pat for pat :: "'a::ucamera upred_f" =
  (match conclusion in "can_be_split (_\<^emph>_) _ _" \<Rightarrow> succeed),
  match (pat) in "rest\<^emph>_" for rest :: "'a upred_f" \<Rightarrow> 
    \<open>((rule persistent_dupl_split', log_prog_solver) 
    | rule can_be_split_sepR), ord_split_pat rest\<close>
  \<bar> "_" \<Rightarrow> \<open>(rule can_be_split_rev, rule can_be_split_refl) 
    | (rule persistent_dupl_split', log_prog_solver)
    | rule can_be_split_baseR\<close>
| (match conclusion in "frame (_\<or>\<^sub>u_) _ _" \<Rightarrow> succeed),rule frame_disj; 
  ord_split_pat pat

method split_log_prog for pat :: "'a::ucamera upred_f" = repeat_new 
  \<open>(rule split_rule | (((match conclusion in "can_be_split head _ _" for head :: "'a upred_f" \<Rightarrow>
    \<open>find_in_pat_sep pat head\<close>), rule can_be_split_baseR) | rule can_be_split_baseL))\<close>
  
text \<open>Linear-time moving that doesn't guarantee the order of the moved parts 
  or that all parts of the pattern where found. Takes an I-pattern.\<close>
method split_move for pat :: "'a::ucamera upred_f" =
  rule upred_entails_trans[OF upred_entail_eqL[OF can_be_splitE]], split_log_prog pat,
  check_not_headL upred_emp, remove_emp
  
method split_move_ord for pat :: "'a::ucamera upred_f" =
  split_move pat, check_move_all True pat

text \<open>Uses the rule to do a step and separates arguments based on the pat.\<close>
method iApply_step' for pat :: "'a::ucamera upred_f" uses rule =
  check_move_all True pat, rule split_trans_rule[OF rule], rule can_be_split_rev,
  ord_split_pat pat; (simp_all only: upred_sep_assoc_eq)?

method iApply_step for pat :: "'a::ucamera upred_f" uses rule =
  rule split_trans_rule[OF rule], rule can_be_split_rev, (* The rule has the order of things reversed. *)
  split_pat pat; remove_emp
  
text \<open>Does a transitive step with the given step term and separates arguments based on pat.\<close>
method iApply_step2' for step pat :: "'a::ucamera upred_f" =
  check_move_all True pat, rule split_trans[where ?Q = step], rule can_be_split_rev,
  ord_split_pat pat; (simp_all only: upred_sep_assoc_eq)?

method iApply_step2 for step pat :: "'a::ucamera upred_f" =
  rule split_trans[where ?Q = step], rule can_be_split_rev, (* The rule has the order of things reversed. *)
  split_pat pat; remove_emp

text \<open>Search for a wand with left hand side lhs_pat, obtain the lhs term from other hypotheses
  matching pat and apply the wand to the newly obtained lhs term.\<close>
method iApply_wand_as_rule for lhs_pat pat :: "'a::ucamera upred_f" =
  check_moveL "lhs_pat-\<^emph>?a_schematic_variable_name_that_noone_would_use_in_setp_pat";
  match conclusion in "_\<^emph>(step_trm-\<^emph>P)\<turnstile>_" for step_trm P :: "'a upred_f" \<Rightarrow>
    \<open>iApply_step2 step_trm pat,
    prefer_last,
      move_sepL step_trm, move_sepL "step_trm-\<^emph>P", subst_pers_keepL rule: upred_wand_apply,
    defer_tac\<close>
  
method iExistsL =
  check_moveL "upred_exists ?P", (rule pull_exists_antecedentR)+; rule upred_existsE';
    (simp only: upred_sep_assoc_eq)?

method iExistsR for inst =
  check_moveR "upred_exists ?P"; (unfold pull_exists_eq pull_exists_eq')?; 
  rule upred_existsI[of _ _ inst]; (simp only: upred_sep_assoc_eq)?
    
method iPureL =
  check_moveL "upred_pure ?b", rule upred_pure_impl

method iPureR = 
  check_moveR "upred_pure ?b", rule upred_pureI' upred_pureI; (simp only: simp_thms(6))?; remove_emp
  
method find_applicable_wand for trm :: "'a::ucamera upred_f" =
  match (trm) in "P-\<^emph>Q" for P Q :: "'a upred_f" \<Rightarrow>
    \<open>check_moveL P, dupl_pers, move_sepL "P-\<^emph>Q"\<close>
  \<bar> "rest\<^emph>(P-\<^emph>Q)" for P Q rest :: "'a upred_f" \<Rightarrow>
    \<open>(check_moveL P, dupl_pers, move_sepL "P-\<^emph>Q") | find_applicable_wand rest\<close>
  \<bar> "rest\<^emph>_" for rest :: "'a upred_f" \<Rightarrow> \<open>find_applicable_wand rest\<close>

method iApply_wand =
  match conclusion in \<open>hyps \<turnstile> _\<close> for hyps \<Rightarrow>
    \<open>find_applicable_wand hyps, subst_pers_keepL rule: upred_wand_apply, remove_emp\<close>
    
text \<open>Tries to remove the head goal term by either framing or reasoning with iPure and assumptions.\<close>
method iFrame_single = 
  remove_emp, match conclusion in \<open>_ \<turnstile> goal\<close> for goal :: "'a::ucamera upred_f" \<Rightarrow>
    \<open> match (goal) in "_\<^emph>P" for P \<Rightarrow> 
        \<open> (check_moveL P; dupl_pers; rule upred_frame upred_emp_left)
        | (iPureR; (assumption | simp))\<close>
      \<bar> P for P :: "'a upred_f" \<Rightarrow> 
        \<open>(move_sepL P; (rule upred_entails_refl | rule upred_weakeningR)) 
         | (iPureR; (assumption | simp))\<close> \<close>
    
method later_elim =
  check_moveL "\<triangleright> ?P", 
  (rule elim_modal_entails'[OF elim_modal_timeless']
  | rule elim_modal_entails[OF elim_modal_timeless']),
  log_prog_solver, log_prog_solver (* Once for the timeless goal, once for the is_except_zero goal. *)

method iMod_raw methods later fupd uses rule =
  iApply rule: rule, (prefer_last, (later | fupd)+, defer_tac)?, remove_emp

method iMod_raw_wand for lhs_pat pat :: "'a::ucamera upred_f" methods later fupd =
  iApply_wand_as_rule lhs_pat pat, (prefer_last, (later | fupd)+, defer_tac)?, remove_emp

text \<open>Applies the given rule and destructs the resulting term.\<close>
method iDestruct uses rule =
  iApply rule: rule, (prefer_last, (iPureL | iExistsL)+, defer_tac)?, remove_emp

method iDrop for pat :: "'a::ucamera upred_f" =
  check_moveL pat; rule upred_entails_trans[OF upred_weakeningL]  
  
lemma test_lemma: "S \<^emph> (\<box>P) \<^emph> Q \<^emph> ((\<box>P)-\<^emph>\<box>R) \<^emph> (\<triangleright>R) -\<^emph> (\<box>R) \<^emph> (\<triangleright>R) \<^emph> Q"
apply iIntro
apply iApply_wand
apply (split_move "Q\<^emph>S\<^emph>\<box>P")
by iFrame_single+
end