theory Misc
imports BaseLogicShallow
begin

definition map_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<times>'v\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "map_heap h f a = folding_on.F f a {(l,v) |l v. h l = Some v}"

definition sep_map_heap :: "('l\<rightharpoonup>'v::ofe) \<Rightarrow> ('l\<times>'v\<Rightarrow>('a::ucamera) iprop) \<Rightarrow> 'a iprop" where
  "sep_map_heap h f = map_heap h (\<lambda>lv a. a \<^emph> f lv) (\<upharpoonleft>True)"

definition sep_map_set :: "('b\<Rightarrow>('a::ucamera) iprop) \<Rightarrow> 'b set \<Rightarrow> 'a iprop" where
  "sep_map_set f s = folding_on.F (\<lambda>x a. a \<^emph> f x) (\<upharpoonleft>True) s"
end