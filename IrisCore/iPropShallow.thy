theory iPropShallow                                                      
imports DerivedConstructions "../SpanningTree/SpanningTreeCameras" Namespace
  ProofSearchPredicates "../HeapLang/PrimitiveLaws" View ProphMap
begin

(*
  The functorial definition of iprop is as follows (unused arguments omitted):

  gmapF := ((loc\<rightharpoonup>((loc option\<times>loc option) ex))\<times>frac) option auth
  markingF := loc set auth
  b invF := (name\<rightharpoonup>b later ag) auth
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
  val resFN = Binding.name "resF"
  val invN = Binding.name "inv"
  val resN = Binding.name "res"
  val ipropN = Binding.name "iprop"
  val getter_prefix = "get_"
  val constructor_prefix = "constr_"
  val gnameN = "name"
  val mapN = "map_res"

  (* Types *)
  val pre_ipropT = \<^typ>\<open>pre_iprop\<close>
  val gnameT = \<^typ>\<open>gname\<close>
  fun mk_opt T = Type (\<^type_name>\<open>option\<close>, [T])
  fun mk_res_mapT res = gnameT --> mk_opt res (* This might need to be (gname,res) fmap *)
  val invT = \<^typ>\<open>'a pre_inv\<close>
  val heapT = \<^typ>\<open>heap_lang_heap\<close>
  val cinvT = \<^typ>\<open>frac option\<close>
  val aT = \<^typ>\<open>'a\<close>
  val base_cameraT = HOLogic.mk_prodT (mk_res_mapT cinvT, 
    HOLogic.mk_prodT (mk_res_mapT invT, mk_res_mapT heapT))
  
  fun mk_pred cmraT = typ_subst_atomic [(aT,cmraT)] \<^typ>\<open>'a upred_f\<close>
  fun subst_aT fp cmraT = typ_subst_atomic [(aT,fp)] cmraT
  fun add_cameraT cmraT cmrasT = HOLogic.mk_prodT (cmraT,cmrasT)
  fun fixed_cmras preT = [
    {camera = cinvT, name = "cinv", getter = NONE, constructor = NONE},
    {camera = subst_aT preT invT, name = "inv", getter = NONE, constructor = NONE},
    {camera = heapT, name = "heap", getter = NONE, constructor = NONE}
   ]
  val mk_cmraT = curry (Library.foldr (uncurry add_cameraT))
  val mk_maps = map mk_res_mapT

  (* Setup to generate getters for single cameras from the camera product *)
  val gname_param = Free (gnameN, gnameT)
  fun mk_def trm lthy = let val prop_trm = HOLogic.mk_Trueprop trm
    in Specification.definition NONE [] [] ((Binding.empty,[]), prop_trm) lthy |> snd end

  fun mk_defs (cmras_data:cameras_data) lthy =
    let fun mk_getter name cmraT = 
          Free (getter_prefix ^ name, [gnameT, the (#cmraPT cmras_data)]--->mk_opt cmraT)$gname_param
        fun mk_own name cmraT = 
          Free (constructor_prefix ^ name, [gnameT,cmraT]--->(the (#cmraPT cmras_data)))$gname_param$
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
  val map_param = Bound 0
  val lookup_name = Abs (mapN, dummyT, map_param$gname_param)
  fun mk_some trm = Const (\<^const_name>\<open>Some\<close>, dummyT-->mk_opt dummyT)$trm
  fun mk_singleton_map res = 
    Const (\<^const_name>\<open>fun_upd\<close>, [mk_res_mapT dummyT,gnameT,dummyT]--->mk_res_mapT dummyT)
    $Const ("Map.empty", mk_res_mapT dummyT)
    $gname_param$(mk_some res)
  fun mk_comp_lookup getter = Const (\<^const_name>\<open>comp\<close>, dummyT)$lookup_name$getter

  fun mk_getter levels is_heap = 
    let val base = if is_heap then dummy_I else dummy_fst
      fun add_level 0 = base
        | add_level n = dummy_comp$(add_level (n-1))$dummy_snd
    in mk_comp_lookup (add_level levels) end

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
    let val base = if is_heap then mk_singleton_map dummy_cmra_object 
      else curry HOLogic.mk_prod (mk_singleton_map dummy_cmra_object) dummy_eps
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
  fun def_resF cmraT = (#2 o Typedecl.abbrev_global (resFN,["'a", "'b"],NoSyn) cmraT)
  fun def_inv preT = (#2 o Typedecl.abbrev_global (invN,[],NoSyn) (subst_aT preT invT))
  fun def_res cmraT = (#2 o Typedecl.abbrev_global (resN,[],NoSyn) cmraT)
  fun def_iprop cmraT = (#2 o Typedecl.abbrev_global (ipropN,[],NoSyn) (mk_pred cmraT))

  fun wrap_quick_and_dirtys_mode f thy =
    let val qad = Config.get_global thy quick_and_dirty in
      thy |> Config.put_global quick_and_dirty true |> f |> Config.put_global quick_and_dirty qad 
    end

  in

  fun mk_iprop cmras thy = 
    let 
      val cmras_raw = map (fn (cmra,name)=>{camera=cmra, name=name, getter=NONE, constructor=NONE}) cmras
      val cmra_data = {number = length cmras+3, cameras = cmras_raw@fixed_cmras pre_ipropT, cmraPT = NONE}
      val cmra_data = mk_getters cmra_data
      val cmra_data = mk_owns cmra_data
      val cmraT = subst_aT pre_ipropT base_cameraT |> mk_cmraT (mk_maps (map fst cmras))
      val cmra_data = {number = #number cmra_data, cameras = #cameras cmra_data, cmraPT = SOME cmraT}
    in thy |> 
      wrap_quick_and_dirtys_mode (fn thy => thy
        |> def_resF cmraT |> def_inv pre_ipropT |> def_res cmraT |> def_iprop cmraT
        |> Named_Target.theory_map (mk_defs cmra_data)
      )
    end
end;
\<close>

type_synonym lockG = "unit ex"

setup \<open>mk_iprop [(\<^typ>\<open>graphUR auth\<close>, "graph"), (\<^typ>\<open>markingUR auth\<close>, "markings"), 
  (\<^typ>\<open>heap_lang_proph_map\<close>, "proph"), (\<^typ>\<open>lockG\<close>, "lock")]\<close>
  
text \<open>Again some experiments wrt the iprop fixed-point\<close>
definition inv_map :: "('a::cofe \<Rightarrow> 'b::cofe) \<Rightarrow> ('a pre_inv \<Rightarrow> 'b pre_inv)" where 
  "inv_map (f::'a\<Rightarrow>'b) = map_prod (map_map_view (map_later f)) id"

lift_definition marking_map :: "('a::cofe -n> 'b::cofe) \<Rightarrow> (markingUR auth -n> markingUR auth)" is
  "\<lambda>_. id" by (rule discrete_ne)

lemma "contractive marking_map"
  unfolding contr_contr_alt contractive_alt_def
  apply transfer by (simp add: ofe_refl)

lift_definition later_map :: "('a::cofe -n> 'b::cofe) \<Rightarrow> ('a later -n> 'b later)" is
  "\<lambda>(f::'a\<Rightarrow>'b) (l::'a later). map_later f l"
  unfolding non_expansive_def
  by (auto simp: n_equiv_later_def later.map_sel)

lemma contr_later: "contractive later_map"
  unfolding contr_contr_alt contractive_alt_def
  apply transfer by (auto simp: later.map_sel n_equiv_later_def split: nat.split)

lemma "contr_ne f \<Longrightarrow> contr_ne (later_map f)"
apply transfer
unfolding contr_contr_alt contractive_alt_def non_expansive_def
apply (auto simp: later.map_sel n_equiv_later_def split: nat.splits)
by (metis Suc_pred)

lift_definition ag_map :: "('a::cofe -n> 'b::cofe) \<Rightarrow> ('a ag -n> 'b ag)" is
  "\<lambda>(f::'a\<Rightarrow>'b) (a::'a ag). map_ag f a"
  unfolding non_expansive_def
  apply (auto simp: n_equiv_ag_def)
  apply (smt (verit, best) image_iff map_ag.rep_eq)
  by (smt (verit, best) ag.set_map image_iff)

lemma "contr_ne f \<Longrightarrow> contr_ne (ag_map f)"
apply transfer
unfolding contr_contr_alt contractive_alt_def non_expansive_def
apply (auto simp: non_expansive_def n_equiv_ag_def image_iff map_ag.rep_eq ag.set_map split: nat.splits)
using Rep_ag apply fastforce
using Rep_ag apply fastforce
by metis+

lift_definition ag_map_contr :: "('a::cofe -n> 'b::cofe) -c> ('a later -n> 'b later)" is
  "later_map" by (rule contr_later)
  
locale T_iso = 
fixes to_iso :: "'a::ofe \<Rightarrow> 'b::ofe" and from_iso :: "'b \<Rightarrow> 'a"
assumes isomorph1: "ofe_eq (to_iso (from_iso x)) x" and isomorph2: "ofe_eq (from_iso (to_iso y)) y"
  and to_ne: "non_expansive to_iso" and from_ne: "non_expansive from_iso"
  
lemma 
assumes iso: "T_iso to from"
shows "n_equiv n x y \<longleftrightarrow> n_equiv n (to x) (to y)"
proof 
assume "n_equiv n x y"
from non_expansiveE[OF T_iso.to_ne[OF iso], OF this] show "n_equiv n (to x) (to y)" by simp
next
assume "n_equiv n (to x) (to y)"
from non_expansiveE[OF T_iso.from_ne[OF iso], OF this] have "n_equiv n (from (to x)) (from (to y))" 
  by simp
with T_iso.isomorph2[OF iso] show "n_equiv n x y"
by (meson ofe_eq_equiv ofe_trans_eqL)
qed
  
lemma "\<exists>(to_iso::markingUR auth\<Rightarrow>markingUR auth) from_iso. T_iso to_iso from_iso"
proof -
have "T_iso (id::markingUR auth \<Rightarrow> markingUR auth) id"
  by (auto simp: T_iso_def ofe_refl non_expansive_def ofe_limit)
then show ?thesis by auto
qed

consts isos :: "('a::ofe pre_inv \<Rightarrow> 'a) \<times>('a \<Rightarrow> 'a pre_inv)"
specification (isos)
  is_iso: "T_iso (fst isos) (snd isos)"
  sorry

text \<open>inG instance examples\<close>
interpretation idInG: inG "\<lambda>\<gamma> (m::gname \<rightharpoonup> 'a::ucamera). m \<gamma>" "\<lambda>\<gamma> x. [\<gamma>\<mapsto>x]"
apply (auto simp: inG_def prod_n_valid_def \<epsilon>_n_valid op_prod_def \<epsilon>_left_id)
apply (auto simp: pcore_prod_def pcore_fun_def \<epsilon>_fun_def \<epsilon>_option_def pcore_option_def comp_def 
  split: option.splits)
using singleton_map_only_n_equiv by metis

interpretation invInG: inG get_inv constr_inv
  apply (auto simp: inG_def get_inv_def constr_inv_def dest!: singleton_map_only_n_equiv)
  apply (auto simp: d_equiv n_equiv_fun_def n_equiv_option_def prod_n_valid_def \<epsilon>_n_valid op_prod_def \<epsilon>_left_id)
  by (auto simp: pcore_prod_def pcore_fun_def \<epsilon>_fun_def \<epsilon>_option_def pcore_option_def comp_def 
    constr_inv_def split: option.splits)

global_interpretation lockInG: inG get_lock constr_lock
apply (auto simp: get_lock_def constr_lock_def d_equiv inG_def prod_n_valid_def \<epsilon>_n_valid op_prod_def
  \<epsilon>_left_id intro: map_upd_eqD1)
by (auto simp: pcore_prod_def pcore_fun_def \<epsilon>_fun_def \<epsilon>_option_def pcore_option_def comp_def
  constr_lock_def singleton_map_n_incl split: option.splits)

global_interpretation prophInG: inG get_proph constr_proph
apply (auto simp: get_proph_def constr_proph_def d_equiv inG_def prod_n_valid_def \<epsilon>_n_valid op_prod_def
  \<epsilon>_left_id intro: map_upd_eqD1)
by (auto simp: pcore_prod_def pcore_fun_def \<epsilon>_fun_def \<epsilon>_option_def pcore_option_def comp_def
  constr_proph_def singleton_map_n_incl split: option.splits)

context begin
private lemma testlemma: "inG (getter::gname\<Rightarrow>'a::ucamera\<Rightarrow>lockG option) put
  \<Longrightarrow> 1=2" sorry
  
thm testlemma[OF lockInG.inG_axioms]
end
end