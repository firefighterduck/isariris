theory SpanningTreeCameras
imports Graph
  "../IrisCore/Frac"
  "../HeapLang/HeapLang"
  "../HeapLang/PrimitiveLaws"
  "../IrisCore/BaseLogicShallow"
begin

(* Children locations, in Coq it's a leibniz0 structure*)
type_synonym chl = "loc option\<times>loc option"

(* The graph camera, a unital camera. *)
type_synonym graphUR = "((loc\<rightharpoonup>(chl ex))\<times>frac) option"

(* A camera for duplicatable markings *)
type_synonym markingUR = "loc set"

(* 
  This would normally be a list of camera functors to allow for modular reasoning.
  Isabelle does not support type lists and thus we use a tuple for this simple example.  
*)
type_synonym graphG = "(graphUR auth \<times> markingUR auth) heapGCmra"

abbreviation own_graph :: "graphUR auth \<Rightarrow> graphG iprop" ("Own\<^sub>g _") where
  "own_graph \<equiv> \<lambda>g. own_other(g, \<epsilon>)"
abbreviation own_marking :: "markingUR auth \<Rightarrow> graphG iprop" ("Own\<^sub>m _") where
  "own_marking \<equiv> \<lambda>m. own_other(\<epsilon>, m)"


context includes points_to_syntax begin
lemma  "upred_holds (((l \<mapsto>{dq} v)::graphG iprop) -\<^emph> \<upharpoonleft>(valid dq))" by (rule points_to_valid)
end
end