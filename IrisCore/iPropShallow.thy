theory iPropShallow
imports CoreStructures DerivedConstructions "../SpanningTree/SpanningTreeCameras" Namespace
  BaseLogicShallow  
begin

text \<open>
  The functorial definition of iprop is as follows (unused arguments omitted):

  gampF := ((loc\<rightharpoonup>((loc option\<times>loc option) ex))\<times>frac) option auth
  markingF := loc set auth
  b invF := (name\<rightharpoonup>b later ag)  auth
  heapF := (loc\<rightharpoonup>(dfrac\<times>val ag)) auth
  (b,_) resf := gmapF \<times> markingF \<times> b invF \<times> heapF
  iprop := (iprop,iprop) resf upred
\<close>

type_synonym 'a pre_inv = "(name\<rightharpoonup>'a later ag) auth \<times> name dset \<times> name dfset"
type_synonym ('a,'b) resF = "graphUR auth \<times> markingUR auth \<times> 'a pre_inv \<times> heapGS"

text \<open> Axiomatic fixed point definition of iprop.\<close>
typedecl pre_iprop
instance pre_iprop :: ofe sorry
type_synonym inv = "pre_iprop pre_inv"
type_synonym res = "(pre_iprop,pre_iprop) resF"
type_synonym res_pred = "res upred_f"

typedef (overloaded) iprop = "UNIV::res_pred set" morphisms pred iProp ..
declare [[coercion iProp]]

setup_lifting type_definition_iprop

lift_definition iPure :: "bool \<Rightarrow> iprop" ("\<upharpoonleft>_") is "upred_pure::bool \<Rightarrow> res_pred" .
lift_definition iOwn :: "res \<Rightarrow> iprop" ("Own(_)") is "upred_own::res \<Rightarrow> res_pred" .
end