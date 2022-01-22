theory Spawn
imports HeapLang Notation
begin

subsection \<open> Spawn and Join \<close>
text \<open> More sophisticated concurrent primitives,
  based on \<^url>\<open>https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/lib/spawn.v\<close>\<close>

definition spawn :: val where "spawn \<equiv>
  V\<lambda> Some ''f'':
    let: Some ''c'' := Alloc NoneE in
    ((Fork ((Var ''c'') \<leftarrow> (SomeE (App (Var ''f'') UnitE)))) ;; (Var ''c'')) endlet"

definition join :: val where "join \<equiv> 
  RecV (Some ''join'') (Some ''c'') 
    match: !(Var ''c'') with
      NoneCase \<Rightarrow> App (Var ''join'') (Var ''c'')
    | SomeCase Some ''x'' \<Rightarrow> Var ''x''
    endmatch"

(* For some reason, spawn needs exclusive units. *)
type_synonym spawnG = "unit ex"    
end