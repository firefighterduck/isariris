theory iPropShallow                                                      
imports DerivedConstructions "../SpanningTree/SpanningTreeCameras" Namespace
  ProofRules "../HeapLang/PrimitiveLaws" View ProphMap
begin

(*
  The functorial definition of iprop is as follows (unused arguments omitted):

  gmapF := ((loc\<rightharpoonup>((loc option\<times>loc option) ex))\<times>frac) option auth
  markingF := loc set auth
  b invF := (name\<rightharpoonup>b later ag)  auth
  heapF := (loc\<rightharpoonup>(dfrac\<times>val ag)) auth
  (b,_) resF := gmapF \<times> markingF \<times> b invF \<times> heapF
  iprop := (iprop,iprop) resF upred
*)

type_synonym 'a pre_inv = "(name, 'a later) map_view \<times> name dset \<times> name dfset"

ML \<open>
  local
  type camera_data = {
    camera: typ,
    name: string,
    getter: term option,
    constructor: term option
  }

  type cameras_data = {
    number: int,
    cameras: camera_data list,
    cmraPT: typ option
  }

    (* Names *)
  val iPropN = Binding.name "iProp"
  val preN = Binding.name "pre"
  val pre_ipropN = Binding.name "pre_iprop"
  val resFN = Binding.name "resF"
  val invN = Binding.name "inv"
  val resN = Binding.name "res"
  val ipropN = Binding.name "iprop"
  val getter_prefix = "get_"
  val constructor_prefix = "constr_"

  (* Types *)
  val invT = \<^typ>\<open>'a pre_inv\<close>
  val heapT = \<^typ>\<open>heap_lang_heap\<close>
  val cinvT = \<^typ>\<open>frac option\<close>
  val aT = \<^typ>\<open>'a\<close>
  val base_cameraT = HOLogic.mk_prodT (cinvT, HOLogic.mk_prodT (invT, heapT))
  
  fun mk_pred cmraT = typ_subst_atomic [(aT,cmraT)] \<^typ>\<open>'a upred_f\<close>
  fun subst_aT fp cmraT = typ_subst_atomic [(aT,fp)] cmraT
  fun add_cameraT cmraT cmrasT = HOLogic.mk_prodT (cmraT,cmrasT)
  fun fixed_cmras preT = [
    {camera = cinvT, name = "cinv", getter = NONE, constructor = NONE},
    {camera = subst_aT preT invT, name = "inv", getter = NONE, constructor = NONE},
    {camera = heapT, name = "heap", getter = NONE, constructor = NONE}
   ]
  val mk_cmraT = curry (Library.foldr (uncurry add_cameraT))

  (* Setup to generate getters for single cameras from the camera product *)
  fun mk_def trm lthy = let val prop_trm = HOLogic.mk_Trueprop trm
    in Specification.definition NONE [] [] ((Binding.empty,[]), prop_trm) lthy |> snd end

  fun mk_defs (cmras_data:cameras_data) lthy =
    let fun mk_getter name cmraT = Free (getter_prefix ^ name, (the (#cmraPT cmras_data))-->cmraT)
        fun mk_own name cmraT = Free (constructor_prefix ^ name, cmraT-->(the (#cmraPT cmras_data)))$
          Free (Binding.name_of resN, cmraT)
    in
      Library.foldl (fn (lthy, cmra_data:camera_data) => 
        (mk_def (curry HOLogic.mk_eq (mk_getter (#name cmra_data) (#camera cmra_data)) 
          (the (#getter cmra_data))) 
       #> mk_def (curry HOLogic.mk_eq (mk_own (#name cmra_data) (#camera cmra_data)) 
          (the (#constructor cmra_data))))
       lthy)
      (lthy, #cameras cmras_data)
    end

  val dummy_fst = Const (\<^const_name>\<open>fst\<close>, dummyT)
  val dummy_snd = Const (\<^const_name>\<open>snd\<close>, dummyT)
  val dummy_comp = Const (\<^const_name>\<open>comp\<close>, dummyT)
  val dummy_I = Const (\<^const_name>\<open>id\<close>, dummyT)
  val dummy_eps = Const (\<^const_name>\<open>\<epsilon>\<close>, dummyT)
  val dummy_cmra_object = Free (Binding.name_of resN, dummyT)

  fun mk_getter levels is_heap = 
    let val base = if is_heap then dummy_I else dummy_fst
      fun add_level 0 = base
        | add_level n = dummy_comp$(add_level (n-1))$dummy_snd
    in add_level levels end

  fun mk_getters ({ number, cameras, cmraPT}: cameras_data) = let
    fun mk_getters_levels _ _ [] = []
      | mk_getters_levels levels n ((cmra: camera_data)::cameras) = 
        {camera = #camera cmra, name = #name cmra,
          getter= if n=levels then SOME (mk_getter n true) else SOME (mk_getter n false),
          constructor = #constructor cmra
        }::(mk_getters_levels levels (n+1) cameras)
    in { number = number, cameras = mk_getters_levels (number-1) 0 cameras, cmraPT = cmraPT }
    end

  fun mk_own levels is_heap =
    let val base = if is_heap then dummy_cmra_object 
      else curry HOLogic.mk_prod dummy_cmra_object dummy_eps
      fun add_level 0 = base
        | add_level n = curry HOLogic.mk_prod dummy_eps (add_level (n-1))
    in add_level levels end

    fun mk_owns ({ number, cameras, cmraPT}: cameras_data) = let
    fun mk_owns_levels _ _ [] = []
      | mk_owns_levels levels n ((cmra: camera_data)::cameras) = 
        {camera = #camera cmra, name = #name cmra,
          getter = #getter cmra,
          constructor = if n=levels then SOME (mk_own n true) else SOME (mk_own n false)
        }::(mk_owns_levels levels (n+1) cameras)
    in { number = number, cameras = mk_owns_levels (number-1) 0 cameras, cmraPT = cmraPT }
    end

  (* Setup functions *)
  val mk_pre_iprop = Typedecl.typedecl_global {final=false} (pre_ipropN,[],NoSyn)

  fun mk_axioms preT propT = 
    [(iPropN,SOME (preT --> propT),NoSyn),(preN,SOME (propT --> preT) ,NoSyn)]
  fun def_axioms ax_defs = (#2 o Specification.axiomatization ax_defs [] [] [])

  fun def_resF cmraT = (#2 o Typedecl.abbrev_global (resFN,["'a", "'b"],NoSyn) cmraT)
  fun def_inv preT = (#2 o Typedecl.abbrev_global (invN,[],NoSyn) (subst_aT preT invT))
  fun def_res cmraT = (#2 o Typedecl.abbrev_global (resN,[],NoSyn) cmraT)
  fun def_iprop cmraT = (#2 o Typedecl.abbrev_global (ipropN,[],NoSyn) (mk_pred cmraT))

  (* Axiomatize that pre_iprop is of class ofe. This will mark the command with a red background. *)
  fun pre_inst thy = Class.instance_arity_cmd ([Binding.name_of pre_ipropN], [], "ofe") thy
    |> Proof.global_skip_proof false |> Proof_Context.theory_of
  in

  fun mk_iprop cmras thy = 
    let val (preT,thy') = mk_pre_iprop thy 
      val cmras_raw = map (fn (cmra,name)=>{camera=cmra, name=name, getter=NONE, constructor=NONE}) cmras
      val cmra_data = {number = length cmras+3, cameras = cmras_raw@fixed_cmras preT, cmraPT = NONE}
      val cmra_data = mk_getters cmra_data
      val cmra_data = mk_owns cmra_data
      val cmraT = subst_aT preT base_cameraT |> mk_cmraT (map fst cmras)
      val propT = mk_pred cmraT 
      val axs = mk_axioms preT propT
      val cmra_data = {number = #number cmra_data, cameras = #cameras cmra_data, cmraPT = SOME cmraT}
    in thy' |> Config.put_global quick_and_dirty true
      |> def_axioms axs |> def_resF cmraT |> def_inv preT |> def_res cmraT |> def_iprop cmraT
      |> pre_inst |> Named_Target.theory_map (mk_defs cmra_data)
      |> Config.put_global quick_and_dirty false
    end
end;
\<close>

setup \<open>mk_iprop [(\<^typ>\<open>graphUR auth\<close>, "graph"), (\<^typ>\<open>markingUR auth\<close>, "markings"), 
  (\<^typ>\<open>heap_lang_proph_map\<close>, "proph")]\<close>

lemma iprop_fp: "iProp (pre P) = P" sorry
declare [[coercion iProp]]

lemma n_equiv_pre [simp]: "n_equiv n (pre P) (pre Q) \<longleftrightarrow> n_equiv n P Q" sorry
end