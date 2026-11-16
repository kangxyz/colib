import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectBassProjectionAnchor

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.BassProjectionNodes

universe u

example (X : Scheme.{u}) (i : Fin 5) : (overlapNodes X i).1 = (nodes X i).1 := rfl

example (X : Scheme.{u}) (i j : Fin 5) :
    (overlapNodes X i).2.inv ≫ (overlapNodes X j).2.hom =
      (nodes X i).2.inv ≫ (nodes X j).2.hom :=
  overlapNodes_transition X i j

#print axioms AlgebraicGeometry.Scheme.Modules.BassProjectionNodes.overlapNodes_transition
