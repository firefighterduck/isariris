theory ProphMap
imports View
begin

subsubsection \<open>Prophecy variable map\<close>

type_synonym ('p,'v) proph_map = "('p,'v list) fmap"
type_synonym ('p,'v) proph_val_list = "('p\<times>'v) list"
type_synonym ('p,'v) proph_mapGS = "('p, 'v list) map_view"

fun proph_list_resolves :: "('p,'v) proph_val_list \<Rightarrow> 'p \<Rightarrow> 'v list" where
  "proph_list_resolves [] _ = []"
| "proph_list_resolves ((q,v)#pvs) p = (if p=q then v#(proph_list_resolves pvs p)
    else proph_list_resolves pvs p)"

definition proph_resolves_in_list :: "('p,'v) proph_map \<Rightarrow> ('p,'v) proph_val_list \<Rightarrow> bool" where
  "proph_resolves_in_list m pvs = fmpred (\<lambda>p vs. vs = proph_list_resolves pvs p) m"
end
