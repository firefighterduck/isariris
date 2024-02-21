theory SpanningTreeCameras
imports Graph
  "../IrisCore/Frac"
  "../HeapLang/HeapLang"
begin

(* Children locations, in Coq it's a leibniz0 structure*)
type_synonym chl = "loc option\<times>loc option"

(* The graph camera, a unital camera. *)
type_synonym graphUR = "(((loc,(chl ex))fmap)\<times>frac) option"

(* A camera for duplicable markings *)
type_synonym markingUR = "loc fset"
end