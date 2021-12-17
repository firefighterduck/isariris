theory PointTo
imports DerivedConstructions Frac BaseLogicShallow
begin

(* 
  What do we need? - a points-to fact for HeapLang
  What does Iris/Coq provide? - a generic heap with points-to based on ghost maps
  What would we need to port this? - the view, gmap_view, ghost_map, resercation_map, dfrac
    and gen_heap cameras (HeapLang also uses gen_heap_inv)
  Is it possible to simplify this by loosing generality? - I guess so
  
  What does gen_heap do? 
    - standard point-to connective that tracks value at a location
    - meta/ghost data at location
    - meta-token to symbolize that no meta data has been associated with location
    - meta-token can be split for different masks
    - given a token for a mask, one can add meta data for a masked namespace
    - meta data can be associated with multiple ghost names
    - implementation:
    - a gmap_view for the raw locations and values
    - a gmap_view that associates locations with ghost names
    - a reservation_map that holds the actual meta data
    - meta data is encoded as integers (requires class countable)
    - the reservation_map maps a namespace (list of integers) to meta data

  Functions:

  points_to :: "loc \<Rightarrow> dfrac \<Rightarrow> val \<Rightarrow> \<Sigma> iProp" where "points_to l dq v = mapsto l dg (Some v)"
  mapsto :: "'loc \<Rightarrow> dfrac \<Rightarrow> 'val \<Rightarrow> \<Sigma> iProp" where "mapsto l dq v = ghost_map_elem gen_heap_name l dq v"
  ghost_map_elem :: "gname \<Rightarrow> 'key \<Rightarrow> dfrac \<Rightarrow> 'val \<Rightarrow> \<Sigma> iProp" where 
    "ghost_map_elem \<gamma> k dq v = Own_\<gamma>(gmap_view_frag k dq v)"
  gmap_view_frag :: "'key \<Rightarrow> dfrac \<Rightarrow> 'val \<Rightarrow> ('key,'val) gmap_view" where
    "gmap_view_frag k dq v = view_frag [k\<mapsto>(dq,Abs_ag v)]"
  view_frag :: "'b \<Rightarrow> ('a,'b) view" where "view_frag b = View None b"

  ported points_to :: "loc \<Rightarrow> dfrac \<Rightarrow> val \<Rightarrow> iProp" where
    "points_to l dq v = Own([k\<mapsto>(dq, Abs_ag (Some v))])"
  
  Types:

  type_synonym ('key, 'val::ofe) gmap_view = 'key\<rightharpoonup>(dfrac\<times>'val ag)
  datatype ('a,'b) view = View (view_auth_proj: "(dfrac\<times>'a ag) option") (view_frag_proj: 'b)

  NOTE: view is a dependent type that has a relation function between 'a and 'b.
  This can be more or less ported to being a type class, I think?!!?!?!


  PROBLEM!!!! 
  The way that meta data is included in the gen_heap can not simply be transferred to Isabelle.
  This is because the heap tracks meta data from arbitrarily many different cameras.
  They are only known by gname, which is then used to decode the saved meta data correctly.
  But there is no simple way of obtaining a type dynamically based on a constant like a gname in Isabelle.
  The exact gname to camera type translation is done by Own_\<gamma> which picks the correct camera for \<gamma>.

  This doesn't seem to be a problem for the spanning tree example, as it doesn't make use of meta
  data but it is a real big issue for a complete port to Isabelle!
*)

type_synonym ('l,'v) heap = "'l \<rightharpoonup> (dfrac\<times>'v ag)"

definition points_to :: "'l \<Rightarrow> dfrac \<Rightarrow> 'v::ofe \<Rightarrow> ('l,'v option) heap iprop" where
  "points_to l dq v = Own([l\<mapsto>(dq, Abs_ag {Some v})])"

end