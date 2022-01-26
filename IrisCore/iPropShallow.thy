theory iPropShallow                                                      
imports DerivedConstructions "../SpanningTree/SpanningTreeCameras" Namespace
  BaseLogicShallow "../HeapLang/PrimitiveLaws"
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

type_synonym 'a pre_inv = "(name\<rightharpoonup>'a later ag) auth \<times> name dset \<times> name dfset"
type_synonym ('a,'b) resF = "graphUR auth \<times> markingUR auth \<times> 'a pre_inv \<times> heap_lang_heap"

text \<open> Axiomatic fixed point definition of iprop.\<close>
typedecl pre_iprop
instance pre_iprop :: ofe sorry
type_synonym inv = "pre_iprop pre_inv"
type_synonym res = "(pre_iprop,pre_iprop) resF"
type_synonym iprop = "res upred_f"

axiomatization iProp :: "pre_iprop \<Rightarrow> iprop" and pre :: "iprop \<Rightarrow> pre_iprop"
lemma iprop_fp: "iProp (pre P) = P" sorry
declare [[coercion iProp]]
end