theory Automation
imports ProofSearchPredicates "HOL-Eisbach.Eisbach_Tools"
begin

method iIntro = 
  (match conclusion in "upred_holds _" \<Rightarrow> \<open>rule upred_wand_holdsI | subst upred_holds_entails\<close>)?,((rule upred_wandI)+)?

method remove_emp = (simp_all only: upred_sep_assoc_eq emp_rule)?

named_theorems iris_simp

declare upred_sep_assoc_eq[iris_simp]
declare emp_rule[iris_simp]

method iris_simp declares iris_simp = 
  (simp_all add: iris_simp)?

method log_prog_solver =
  fast intro: log_prog_rule
(* | slow intro: log_prog_rule *)
(* | best intro: log_prog_rule *)
(*| force intro: log_prog_rule
| blast 5 intro: log_prog_rule*)

method is_entailment = match conclusion in "_\<turnstile>_" \<Rightarrow> succeed

text \<open>A simple attribute to convert \<^const>\<open>upred_holds\<close> predicates into entailments.\<close>
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
  "Find a subgoal that the method can work on and move it to the top."

text \<open>Find a subgoal on which the given method is applicable and apply the method there.
  This will not move any subgoals around and resulting subgoals will not be at the head. 
  Requires the method to be evaluated for all subgoals at most once.\<close>
method_setup apply_first =
  \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>  
    let fun eval_method i = 
      SELECT_GOAL (method_evaluate m ctxt facts) i
    in SIMPLE_METHOD (FIRSTGOAL eval_method) facts end)\<close>
  "Find the first subgoal that the method can work on."

method_setup get_concl = \<open> let 
  fun get_concl m ctxt facts (ctxt',thm) = let
    fun free_to_var (Free (x, ty)) = (if Variable.is_declared ctxt' x then Free (x,ty) else Var ((x,0),ty))
      | free_to_var t = t
    val frees_to_vars = Term.map_aterms free_to_var
    val trm = Thm.prop_of thm
    val concl = (case try (HOLogic.dest_Trueprop o Logic.concl_of_goal trm) 1 of SOME trm' => trm'
      | NONE => trm) |> frees_to_vars
  in
    case concl of Const (\<^const_name>\<open>Pure.prop\<close>,_)$(Const (\<^const_name>\<open>Pure.term\<close>, _ )$_) 
      => CONTEXT_TACTIC all_tac (ctxt',thm)
    | Const (\<^const_name>\<open>Pure.prop\<close>,_)$_ => CONTEXT_TACTIC no_tac (ctxt',thm)
    | _ => (case try (Method_Closure.apply_method ctxt m [concl] [] [] ctxt facts) (ctxt',thm) of
      SOME res => res | NONE => Seq.empty)
  end
in 
  (Scan.lift Parse.name >> (fn m => fn ctxt => get_concl m ctxt))
end \<close> "Allows to match against conclusions with schematic variables."
  
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
      \<bar> "pat\<^emph>_" \<Rightarrow> \<open>entails_substL rule: upred_sep_comm\<close>
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
  match (trm) in pat \<Rightarrow> fail
  \<bar> "\<diamondop>rest" for rest :: "'a upred_f" \<Rightarrow> \<open>find_other_than_pat_sep pat rest\<close>
  \<bar> "\<triangleright>rest" for rest :: "'a upred_f" \<Rightarrow> \<open>find_other_than_pat_sep pat rest\<close>
  \<bar> "rest\<^emph>head" for rest head :: "'a upred_f" \<Rightarrow> 
    \<open>find_other_than_pat_sep pat rest | find_other_than_pat_sep pat head\<close>
  \<bar> "_" \<Rightarrow> succeed  
  
method check_not_headL for pat :: "'a::ucamera upred_f" =
  match conclusion in "_\<^emph>head\<turnstile>_" for head :: "'a upred_f" \<Rightarrow> \<open>find_other_than_pat_sep pat head\<close>
  
method check_head for pat trm :: "'a::ucamera upred_f" =
  match (pat) in "rest_pat\<^emph>head_pat" for rest_pat head_pat :: "'a upred_f" \<Rightarrow> 
    \<open>match (trm) in "rest\<^emph>head_pat" for rest :: "'a upred_f" \<Rightarrow> \<open>check_head rest_pat rest\<close>\<close>
  \<bar> _ \<Rightarrow> \<open>match (trm) in pat \<Rightarrow> succeed \<bar> "_\<^emph>pat" \<Rightarrow> succeed\<close>

text \<open>Checked move methods, guaranteed to terminate.\<close>
method check_headL for pat :: "'a::ucamera upred_f" =
  match conclusion in "hyps\<turnstile>_" for hyps :: "'a upred_f" \<Rightarrow> \<open>check_head pat hyps\<close>

method check_moveL for pat :: "'a::ucamera upred_f" =
  match conclusion in "hyps\<turnstile>_" for hyps :: "'a upred_f" \<Rightarrow>
    \<open>find_pat_sep pat hyps; move_sepL pat\<close>
    
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
method iApply uses rule = iris_simp,
  match rule[uncurry] in "hyps \<turnstile> _" for hyps \<Rightarrow> \<open>check_move_dupl_all True True hyps, move_sep_all True hyps, 
    subst_pers_keepL rule: rule\<close>
  \<bar> "_ \<Longrightarrow> hyps \<turnstile> _" for hyps \<Rightarrow> \<open>check_move_dupl_all True True hyps, move_sep_all True hyps,
    subst_pers_keepL rule: rule\<close>
  \<bar> R[curry]: "upred_holds _" \<Rightarrow> \<open>iApply rule: R[to_entailment] | rule add_holds[OF rule]\<close>
  \<bar> R[curry]: "_ \<Longrightarrow> upred_holds _" \<Rightarrow> \<open>iApply rule: R[to_entailment]\<close>, iris_simp

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

text \<open>O-pattern based splitting. Can only support a single (possible nested) pattern term at a time.\<close>
method splitO for pat :: "'a::ucamera upred_f" and goal :: "bool" = remove_emp,
  (match (goal) in "can_be_split head _ _" for head \<Rightarrow>
    \<open>match (head) in pat \<Rightarrow> \<open>rule can_be_split_baseR\<close>\<close>) (* Pattern found *)
| match (goal) in "can_be_split (\<triangleright>head) _ _" for head \<Rightarrow>
    \<open>match (pat) in "\<triangleright>rest" for rest :: "'a upred_f" \<Rightarrow> \<open>rule can_be_split_later, 
      splitO rest "can_be_split head ?l ?r"\<close> \<bar> _ \<Rightarrow> \<open>rule can_be_split_baseL\<close>\<close>
  \<bar> "can_be_split (\<diamondop>head) _ _" for head \<Rightarrow>
    \<open>match (pat) in "\<diamondop>rest" for rest :: "'a upred_f" \<Rightarrow> \<open>rule can_be_split_except_zero,
      splitO rest "can_be_split head ?l ?r"\<close> \<bar> _ \<Rightarrow> \<open>rule can_be_split_baseL\<close>\<close>
  \<bar> "can_be_split (tail\<^emph>head) _ _" for head tail \<Rightarrow> 
    \<open>rule can_be_split_mono, splitO pat "can_be_split tail ?l ?r", splitO pat "can_be_split head ?l ?r"\<close>
  \<bar> "can_be_split (l\<or>\<^sub>ur) _ _" for l r \<Rightarrow> 
    \<open>rule can_be_split_disj, splitO pat "can_be_split l ?l ?r", splitO pat "can_be_split r ?l ?r"\<close> 
  \<bar> _ \<Rightarrow> \<open>rule can_be_split_baseL\<close>
    
method split_moveO for pat :: "'a::ucamera upred_f" =
  match conclusion in "hyps\<turnstile>_" for hyps \<Rightarrow> 
  \<open>rule upred_entails_trans[OF upred_entail_eqL[OF can_be_splitE]],
   splitO pat "can_be_split hyps ?l ?r", remove_emp\<close>

method split_move_allO for pat :: "'a::ucamera upred_f" =
  match (pat) in "tail_pat\<^emph>head_pat" for tail_pat head_pat :: "'a upred_f" \<Rightarrow>
    \<open>split_move_allO tail_pat, check_headL tail_pat, split_moveO head_pat\<close>
  \<bar> _ \<Rightarrow> \<open>split_moveO pat, check_headL pat\<close>

lemma "(\<triangleright>((\<diamondop>P)\<^emph>Q)) \<or>\<^sub>u (\<triangleright>\<diamondop>P) \<turnstile> \<triangleright>P" apply (split_moveO "\<triangleright>\<diamondop>P") oops
lemma "\<diamondop>(R\<^emph>\<triangleright>(P\<^emph>Q)) \<turnstile> R" apply (split_moveO "\<diamondop>\<triangleright>(P\<^emph>Q)") oops
lemma "\<diamondop>(R\<^emph>\<triangleright>(P\<^emph>S\<^emph>Q)) \<turnstile> R" apply (split_moveO "\<diamondop>\<triangleright>(P\<^emph>Q)") oops (*Strange*)
lemma "\<diamondop>(R\<^emph>\<triangleright>(P\<^emph>S\<^emph>Q)) \<turnstile> R" apply (split_moveO "\<box>P") oops (*Strange*)
lemma "\<diamondop>(R\<^emph>\<triangleright>(P\<^emph>Q)) \<turnstile> R" apply (split_move_allO "(\<diamondop>\<triangleright>P)\<^emph>\<diamondop>R") oops

text \<open>Uses the \<^term>\<open>rule\<close> to do a step and separates arguments based on the \<^term>\<open>pat\<close>.\<close>
method iApply_step' for pat :: "'a::ucamera upred_f" uses rule = iris_simp,
  check_move_all True pat, rule split_trans_rule[OF rule[to_entailment]], rule can_be_split_rev,
  ord_split_pat pat; iris_simp

method iApply_step for pat :: "'a::ucamera upred_f" uses rule = iris_simp,
  rule split_trans_rule[OF rule[to_entailment]], rule can_be_split_rev, (* The rule has the order of things reversed. *)
  split_pat pat; iris_simp
  
text \<open>Does a transitive step with the given \<^term>\<open>step\<close> and separates arguments based on \<^term>\<open>pat\<close>.\<close>
method iApply_step2' for step pat :: "'a::ucamera upred_f" = iris_simp,
  check_move_all True pat, rule split_trans[where ?Q = step], rule can_be_split_rev,
  ord_split_pat pat; iris_simp

method iApply_step2 for step pat :: "'a::ucamera upred_f" = iris_simp,
  rule split_trans[where ?Q = step], rule can_be_split_rev, (* The rule has the order of things reversed. *)
  split_pat pat; iris_simp

text \<open>Search for a wand with left hand side \<^term>\<open>lhs_pat\<close>, obtain the lhs term from other hypotheses
  matching \<^term>\<open>pat\<close> and apply the wand to the newly obtained lhs term.\<close>
method iApply_wand_as_rule for lhs_pat pat :: "'a::ucamera upred_f" = iris_simp, 
  check_moveL "lhs_pat-\<^emph>?a_schematic_variable_name_that_noone_would_use_in_setp_pat";
  match conclusion in "_\<^emph>(step_trm-\<^emph>P)\<turnstile>_" for step_trm P :: "'a upred_f" \<Rightarrow>
    \<open>iApply_step2 step_trm pat,
    prefer_last,
      move_sepL step_trm, move_sepL "step_trm-\<^emph>P", subst_pers_keepL rule: upred_wand_apply,
    defer_tac\<close>, iris_simp
  
method iExistsL = iris_simp,
  check_moveL "upred_exists ?P", ((rule pull_exists_antecedentR)+)?; rule upred_existsE',
  iris_simp

method iExistsR for inst = iris_simp,
  check_moveR "upred_exists ?P"; (unfold pull_exists_eq pull_exists_eq')?; 
  rule upred_existsI[of _ _ inst], iris_simp

method iForallL for inst = iris_simp,
  check_moveL "upred_forall ?P";
  rule upred_entails_trans[OF upred_forall_inst[of _ inst]] upred_entails_substE[OF upred_forall_inst[of _ inst]], 
  iris_simp
  
method iForallR = iris_simp, check_moveR "upred_forall ?P"; rule upred_forallI, iris_simp
  
method iPureL =
  iris_simp, check_moveL "upred_pure ?b", rule upred_pure_impl, iris_simp

method iPureR = 
  iris_simp, check_moveR "upred_pure ?b", rule upred_pureI' upred_pureI, assumption?, iris_simp
  
method find_applicable_wand for trm :: "'a::ucamera upred_f" =
  match (trm) in "P-\<^emph>Q" for P Q :: "'a upred_f" \<Rightarrow>
    \<open>check_moveL P, dupl_pers, move_sepL "P-\<^emph>Q"\<close>
  \<bar> "rest\<^emph>(P-\<^emph>Q)" for P Q rest :: "'a upred_f" \<Rightarrow>
    \<open>(check_moveL P, dupl_pers, move_sepL "P-\<^emph>Q") | find_applicable_wand rest\<close>
  \<bar> "rest\<^emph>_" for rest :: "'a upred_f" \<Rightarrow> \<open>find_applicable_wand rest\<close>

method iApply_wand = iris_simp,
  match conclusion in \<open>hyps \<turnstile> _\<close> for hyps \<Rightarrow>
    \<open>find_applicable_wand hyps, subst_pers_keepL rule: upred_wand_apply, iris_simp\<close>

method iFrame_single_safe for trm :: bool = iris_simp,
  match (trm) in \<open>_ \<turnstile> goal\<close> for goal \<Rightarrow>
    \<open> match (goal) in "_\<^emph>P" for P \<Rightarrow> 
        \<open>(check_moveL P; dupl_pers; rule upred_frame upred_emp_left) | iPureR\<close>
      \<bar> _ \<Rightarrow>
        \<open>(check_moveL goal; (rule upred_entails_refl | rule upred_weakeningR)) | iPureR\<close> \<close>,
  iris_simp
    
text \<open>Tries to remove the head goal term by either framing or reasoning with iPure and assumptions.\<close>
method iFrame_single = iris_simp, get_concl "Automation.iFrame_single_safe", iris_simp

method iExistsR2 = iris_simp,
  (check_moveR "upred_exists ?P"; (unfold pull_exists_eq pull_exists_eq')?; 
  rule upred_exists_lift, rule exI)+, iris_simp

method later_elim = iris_simp,
  check_moveL "\<triangleright> ?P", 
  (rule elim_modal_entails'[OF elim_modal_timeless']
  | rule elim_modal_entails[OF elim_modal_timeless']),
  log_prog_solver, log_prog_solver (* Once for the timeless goal, once for the is_except_zero goal. *)

method iMod_raw methods later fupd uses rule =
  iris_simp, iApply rule: rule, (prefer_last, (later | fupd)+, defer_tac)?, iris_simp

method iMod_raw_wand for lhs_pat pat :: "'a::ucamera upred_f" methods later fupd =
  iris_simp, iApply_wand_as_rule lhs_pat pat, (prefer_last, (later | fupd)+, defer_tac)?, iris_simp

method iMod_raw_step for pat :: "'a::ucamera upred_f" methods later fupd uses rule = 
  iris_simp, iApply_step pat rule: rule; all \<open>((later | fupd)+)?\<close>; iris_simp
  
method iDestruct_raw = iris_simp,
  ((check_moveL "\<V> (?c::'a::dcamera)", entails_substL rule: upred_entail_eqL[OF discrete_valid])
| iPureL
| iExistsL), iris_simp

text \<open>Applies the given rule and destructs the resulting term.\<close>
method iDestruct uses rule =
  iris_simp, iApply rule: rule, (prefer_last, iDestruct_raw+, defer_tac)?, iris_simp

method iDrop for pat :: "'a::ucamera upred_f" =
  iris_simp, check_moveL pat; rule upred_entails_trans[OF upred_weakeningL], iris_simp
  
lemma test_lemma: "S \<^emph> (\<box>P) \<^emph> Q \<^emph> ((\<box>P)-\<^emph>\<box>R) \<^emph> (\<triangleright>R) -\<^emph> (\<box>R) \<^emph> (\<triangleright>R) \<^emph> Q"
apply iIntro
apply iApply_wand
apply (split_move "Q\<^emph>S\<^emph>\<box>P")
by iFrame_single+
end