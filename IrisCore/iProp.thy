theory iProp
imports DerivedConstructions BaseLogicShallowAlt Frac AuthHeap Misc "../SpanningTree/SpanningTreeCameras"
begin

datatype invGS = Inv "(name\<rightharpoonup>iprop later ag) auth"
  and iprop = iProp "invGS upred"

end