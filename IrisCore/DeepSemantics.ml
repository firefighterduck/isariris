signature UPRED_SEMANTICS =
sig
  exception UnknownVariable
  val print_sem: term -> string list -> typ option -> theory -> theory
  val upred_sem: term -> typ option -> term
  val register_sem: term -> term -> theory -> theory
end;

structure UpredSem: UPRED_SEMANTICS =
struct
  structure SemData = Theory_Data
    (type T = term Symtab.table
      val empty = Symtab.empty
      val merge = Symtab.merge (K true))
  fun lookup thy var = Symtab.lookup (SemData.get thy) (HOLogic.dest_string var)
  fun register_sem k v = SemData.map (Symtab.update (HOLogic.dest_string k, v))

  exception UnknownVariable

  fun mk_all var body = 
    (Const (\<^const_name>\<open>HOL.All\<close>,(dummyT-->\<^typ>\<open>bool\<close>)-->\<^typ>\<open>bool\<close>))$(absfree var body)

  fun mk_ex var body =
    (Const (\<^const_name>\<open>HOL.Ex\<close>,(dummyT-->\<^typ>\<open>bool\<close>)-->\<^typ>\<open>bool\<close>))$(absfree var body)

  fun mk_n_valid x = \<^const>\<open>Rep_sprop\<close>$(Const (\<^const_name>\<open>valid_raw\<close>,dummyT)$x)

  fun mk_n_equiv n x y = (Const (\<^const_name>\<open>n_equiv\<close>,dummyT))$n$x$y

  fun mk_op x y = Const (\<^const_name>\<open>camera_class.op\<close>,dummyT)$x$y

  fun get_new_var var body taken [] thy = 
    let 
      val new_vars = Variable.variant_frees (Proof_Context.init_global thy) [var,body] taken
      val new_var = hd (rev new_vars)
      val thy' = register_sem var (Free new_var) thy
    in (new_var, thy', []) end
  | get_new_var var _ _ (new_var::predef) thy = 
    let val thy' = register_sem var (Free (new_var, dummyT)) thy 
    in ((new_var, dummyT), thy', predef) end

  (* First the uterm semantics *)
  fun term_sem (Const (\<^const_name>\<open>Var\<close>,_)$var) _ _ thy = 
    let val trm = lookup thy var in
      case trm of SOME trm' => (trm', thy) | NONE => 
        ((Syntax.pretty_term (Proof_Context.init_global thy) var |> Pretty.writeln);
        raise UnknownVariable) end
    | term_sem (Const (\<^const_name>\<open>Const\<close>,_)$const) _ _ thy = (const,thy)
    | term_sem (Const (\<^const_name>\<open>App\<close>,_)$f$x) taken predef thy =
      let val (f',thy') = term_sem f taken predef thy; val (x',thy'') = term_sem x taken predef thy'
      in (betapply (f',x'),thy'') end
    | term_sem (Const (\<^const_name>\<open>Abs\<close>,_)$var$body) taken predef thy =
      let val (new_var,thy', predef') = get_new_var var body taken predef thy
        val (body',thy'') = term_sem body (new_var::taken) predef' thy'
      in (absfree new_var body', thy'') end
    | term_sem (Const t) _ _ thy = 
      let val _ = Syntax.pretty_term (Proof_Context.init_global thy) (Const t) |> Pretty.writeln
      in raise TERM("Unsupported term!", [Const t]) end
    | term_sem t _ _ thy = (t,thy)

  (* Now the upred semantics*)
  fun pred_sem (Const (\<^const_name>\<open>Pure\<close>,_)$bt) taken predef thy =
      let val (bt',thy') = term_sem bt taken predef thy val bty = fastype_of bt'
        val pure_pred = absdummy \<^typ>\<open>nat\<close> bt' |> absdummy dummyT
      in if bty=\<^typ>\<open>bool\<close> then (pure_pred,thy') 
        else raise TYPE ("Pure needs bool parameter!", [bty], [bt']) end
    | pred_sem (Const (\<^const_name>\<open>Conj\<close>,_)$p$q) taken predef thy =
      let val (p',thy') = pred_sem p taken predef thy val (q',thy'') = pred_sem q taken predef thy'
        val p'' = betapply (betapply (p',(Free ("x",dummyT))),(Free ("n", \<^typ>\<open>nat\<close>)))
        val q'' = betapply (betapply (q',(Free ("x",dummyT))),(Free ("n", \<^typ>\<open>nat\<close>)))
        val conj_body = \<^const>\<open>HOL.conj\<close>$p''$q''
        val conj_pred = absfree ("n",\<^typ>\<open>nat\<close>) conj_body |> absfree ("x",dummyT)
      in (conj_pred, thy'') end
    | pred_sem (Const (\<^const_name>\<open>Disj\<close>,_)$p$q) taken predef thy =
      let val (p',thy') = pred_sem p taken predef thy val (q',thy'') = pred_sem q taken predef thy'
        val p'' = betapply (betapply (p',(Free ("x",dummyT))),(Free ("n", \<^typ>\<open>nat\<close>)))
        val q'' = betapply (betapply (q',(Free ("x",dummyT))),(Free ("n", \<^typ>\<open>nat\<close>)))
        val conj_body = \<^const>\<open>HOL.disj\<close>$p''$q''
        val conj_pred = absfree ("n",\<^typ>\<open>nat\<close>) conj_body |> absfree ("x",dummyT)
      in (conj_pred, thy'') end
    | pred_sem (Const (\<^const_name>\<open>Forall\<close>,_)$var$body) taken predef thy =
      let val (new_var, thy', predef') = get_new_var var body taken predef thy
        val (body',thy'') = pred_sem body (new_var::taken) predef' thy'
        val pred_body = betapply (betapply (body',(Free ("x",dummyT))),(Free ("n", \<^typ>\<open>nat\<close>)))
        val forall_body = mk_all new_var pred_body
        val forall_pred = absfree ("n",\<^typ>\<open>nat\<close>) forall_body |> absfree ("x",dummyT)
      in (forall_pred, thy'') end
    | pred_sem (Const (\<^const_name>\<open>Exists\<close>,_)$var$body) taken predef thy =
      let val (new_var, thy', predef') = get_new_var var body taken predef thy
        val (body',thy'') = pred_sem body (new_var::taken) predef' thy'
        val pred_body = betapply (betapply (body',(Free ("x",dummyT))),(Free ("n", \<^typ>\<open>nat\<close>)))
        val ex_body = mk_ex new_var pred_body
        val ex_pred = absfree ("n",\<^typ>\<open>nat\<close>) ex_body |> absfree ("x",dummyT)
      in (ex_pred, thy'') end
    | pred_sem (Const (\<^const_name>\<open>Sep\<close>,_)$p$q) taken predef thy =
      let val (p',thy') = pred_sem p taken predef thy val (q',thy'') = pred_sem q taken predef thy'
        val n = Free ("n",\<^typ>\<open>nat\<close>) val b1 = Free ("b1", dummyT) val b2 = Free ("b2",dummyT)
        val p'' = p'$b1$n val q'' = q'$b2$n
        val body = \<^const>\<open>HOL.conj\<close>
          $(mk_n_equiv n (Free ("x",dummyT)) (mk_op b1 b2))
          $(\<^const>\<open>HOL.conj\<close>$p''$q'')
        val sep_body = mk_ex ("b1",dummyT) (mk_ex ("b2",dummyT) body)
        val sep_pred = absfree ("n",\<^typ>\<open>nat\<close>) sep_body |> absfree ("x",dummyT)
       in (sep_pred, thy'') end
    | pred_sem (Const (\<^const_name>\<open>Wand\<close>,_)$p$q) taken predef thy =
      let val (p',thy') = pred_sem p taken predef thy val (q',thy'') = pred_sem q taken predef thy'
        val b = Free ("b",dummyT) val m = Free ("m", \<^typ>\<open>nat\<close>) val x = Free ("x",dummyT)
        val ab = mk_op x b val n = Free ("n", \<^typ>\<open>nat\<close>)
        val body = \<^const>\<open>HOL.implies\<close>$(Const (\<^const_name>\<open>less_eq\<close>,dummyT)$m$n)$
          (\<^const>\<open>HOL.implies\<close>$(mk_n_valid ab$m)$(\<^const>\<open>HOL.implies\<close>$(p'$b$m)$(q'$ab$m)))
        val wand_body  = mk_all ("b", dummyT) (mk_all ("m", \<^typ>\<open>nat\<close>) body)
        val wand_pred = absfree ("n",\<^typ>\<open>nat\<close>) wand_body |> absfree ("x",dummyT)
      in (wand_pred, thy'') end
    | pred_sem (Const (\<^const_name>\<open>OwnU\<close>,_)$x) taken predef thy =
      let val (x',thy') = term_sem x taken predef thy
        val x = ("x", dummyT) val n = ("n", \<^typ>\<open>nat\<close>)
        val body = Const (\<^const_name>\<open>camera_class.n_incl\<close>, dummyT)$(Free n)$x'$(Free x)
        val own_pred = absfree n body |> absfree x
      in (own_pred, thy') end
    | pred_sem (Const (\<^const_name>\<open>Valid\<close>,_)$x) taken predef thy =
      let val (x',thy') = term_sem x taken predef thy val n = ("n", \<^typ>\<open>nat\<close>) 
        val body = mk_n_valid x' |> absfree n |> absdummy dummyT
      in (body, thy') end
    | pred_sem (Const (\<^const_name>\<open>Persistent\<close>,_)$p) taken predef thy =
      let val (p',thy') = pred_sem p taken predef thy val x = ("x",dummyT) val n = ("n", \<^typ>\<open>nat\<close>)
        val body = p'$(Const (\<^const_name>\<open>total_camera_class.core\<close>,dummyT)$Free x)$(Free n)
        val pers_pred = absfree n body |> absfree x
      in (pers_pred, thy') end
    | pred_sem (Const (\<^const_name>\<open>Plain\<close>,_)$p) taken predef thy =
      let val (p',thy') = pred_sem p taken predef thy val n = ("n", \<^typ>\<open>nat\<close>)
        val body = p'$(Const (\<^const_name>\<open>ucamera_class.\<epsilon>\<close>,dummyT))$Free n
        val plain_pred = absfree n body |> absdummy dummyT
      in (plain_pred, thy') end
    | pred_sem (Const (\<^const_name>\<open>Later\<close>,_)$p) taken predef thy =
      let val (p',thy') = pred_sem p taken predef thy val x = ("x",dummyT) val n = ("n", \<^typ>\<open>nat\<close>)
        val body = \<^const>\<open>HOL.disj\<close>$(Const (\<^const_name>\<open>HOL.eq\<close>,dummyT)$Free n$\<^term>\<open>0::nat\<close>)
          $(p'$Free x$(Const (\<^const_name>\<open>minus_class.minus\<close>,dummyT)$Free n$
            Const (\<^const_name>\<open>one_class.one\<close>,\<^typ>\<open>nat\<close>)))
        val later_pred = absfree n body |> absfree x
      in (later_pred, thy') end
    | pred_sem (Const (\<^const_name>\<open>BUpd\<close>,_)$p) taken predef thy =
      let val (p',thy') = pred_sem p taken predef thy
        val m = ("m",\<^typ>\<open>nat\<close>) val n = ("n",\<^typ>\<open>nat\<close>) val x = ("x",dummyT) val y = ("y",dummyT)
        val z = ("z",dummyT)
        val body = \<^const>\<open>HOL.implies\<close>$(Const (\<^const_name>\<open>less_eq\<close>,dummyT)$Free m$Free n)
          $(\<^const>\<open>HOL.implies\<close>$(mk_n_valid (mk_op (Free x) (Free y))$Free m)$(mk_ex z 
            (\<^const>\<open>HOL.conj\<close>$(mk_n_valid (mk_op (Free z) (Free y))$Free m)$(p'$Free z$Free m))))
        val bupd_pred = absfree n body |> absfree x
      in (bupd_pred, thy') end
    | pred_sem t _ _ thy = 
      let val _ = Syntax.pretty_term (Proof_Context.init_global thy) t |> Pretty.writeln
      in raise TERM("Unsupported term!", [t]) end

  fun upred_sem trm cmra = 
    let val cmraT = case cmra of SOME cmraT => cmraT | NONE => TFree ("'a", \<^sort>\<open>ucamera\<close>)
      val a = ("x",cmraT) val n =  ("n",\<^typ>\<open>nat\<close>) 
    in mk_all a (mk_all n (\<^const>\<open>HOL.implies\<close>$ 
        (mk_n_valid (Free a)$(Free n))$(betapply(betapply (trm,(Free a)),Free n))))
    end
    
  fun print_sem trm varnames cmra thy = 
    let val (trm',thy') = pred_sem trm [("y",dummyT)] varnames thy 
        val sem = upred_sem trm' cmra
        val trm'' = Syntax.check_term (Proof_Context.init_global thy') sem
        val _ = Syntax.pretty_term \<^context> trm'' |> Pretty.writeln
    in thy' end
end;

open UpredSem