theory Mon
imports Graph 
  "../IrisCore/DerivedConstructions" 
  "../HeapLang/Locations"
  "../IrisCore/BaseLogicShallow"
begin

subsection \<open> The underlying structures of the spanning tree \<close>
text \<open> Based on https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/spanning_tree/mon.v \<close>

(* Children locations, in Coq it's a leibniz0 structure*)
type_synonym chl = "loc option\<times>loc option"

(* The graph camera, a total or unital camera. *)
type_synonym graphUR = "((loc\<rightharpoonup>chl ex)\<times>frac) option"

(* A camera for duplicatable markings *)
type_synonym markingUR = "loc set"

(* 
  This is a big problem. In Coq, graphG takes a functor list \<Sigma> 
  and makes sure that it contains markingUR auth and graphUR auth.
  By doing so, we can have \<Sigma> iprop that works with both cameras.
  Otherwise we can't combine assertions about both cameras in one
  formula.
 *)
type_synonym graphG = "(markingUR auth,graphUR auth) sum_camera"

lift_definition is_marked ::"loc \<Rightarrow> graphG iprop" is "\<lambda>l. Own(Inl(fragm {l}))"
end