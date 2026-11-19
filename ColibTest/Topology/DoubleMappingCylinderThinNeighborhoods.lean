module

public import Colib.Topology.DoubleMappingCylinder.ThinNeighborhoods

open CategoryTheory Limits MonoidalCategory Topology TopCat TopCat.DoubleCylinder
open scoped Topology unitInterval

universe u

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (EB : PathThinNeighborhoods B) (EC : PathThinNeighborhoods C)

example (d : D) : ∃ V : Set D, IsOpen V ∧ d ∈ V ∧ AmbientPathThin V :=
  exists_open_ambientPathThin f g sq EB EC d

example [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace B]
    [LocallyPathConnectedSpace C] : PathThinNeighborhoods D :=
  pathThinNeighborhoods f g sq EB EC

#print axioms exists_open_ambientPathThin_of_homotopy
#print axioms TopCat.DoubleCylinder.pathThinNeighborhoods
