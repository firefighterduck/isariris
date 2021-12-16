theory Par
imports Spawn
begin

subsection \<open> Parallel execution \<close>
text \<open> Based on https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lib/par.v \<close>

definition par :: val where "par \<equiv>
  V\<lambda> Some ''e1'': E\<lambda> Some ''e2'':
    let: Some ''handle'' := App (Val spawn) (Var ''e1'') in
    let: Some ''v2'' := App (Var ''e2'') UnitE in
    let: Some ''v1'' := App (Val join) (Var ''handle'') in
      Pair (Var ''v1'') (Var ''v2'') tel tel tel"
abbreviation "Par \<equiv> \<lambda>e1 e2. App (App (Val par) (E\<lambda> None: e1)) (E\<lambda> None: e2)"
notation Par ("_|||_")
end