/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.StrictDoubleSquareConeCells
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare.Double
variable (E : Arrow (Arrow (Arrow (Arrow LoopPrespectrum.{u}))))

example (n : ℕ)
    (x : E.right.right.right.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.target (totalFunctor.mapArrow.mapArrow.obj E) n
        (Cell.target E.right.right n x)) =
      Cell.target (coneSquare (comparisonMap E)) n
        (Cell.target ((Arrow.rightFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n x) :=
  interchange_target_target E n x

example (n : ℕ) (t v : unitInterval)
    (x : E.right.right.left.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.target (totalFunctor.mapArrow.mapArrow.obj E) n
        (Cell.overlap E.right.right n t v x)) =
      Cell.overlap (coneSquare (comparisonMap E)) n t v
        (Cell.target ((Arrow.leftFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n x) :=
  interchange_target_overlap E n t v x

example (n : ℕ) (r t : unitInterval)
    (x : E.left.right.right.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.upper (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.lower E.left.right n t x)) =
      Cell.lower (coneSquare (comparisonMap E)) n t
        (Cell.upper ((Arrow.rightFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r x) :=
  interchange_upper_lower E n r t x

example (n : ℕ) (r t : unitInterval)
    (x : E.right.left.left.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.lower (totalFunctor.mapArrow.mapArrow.obj E) n r
        (Cell.upper E.right.left n t x)) =
      Cell.upper (coneSquare (comparisonMap E)) n t
        (Cell.lower ((Arrow.leftFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n r x) :=
  interchange_lower_upper E n r t x

example (n : ℕ) (r s : unitInterval)
    (x : E.left.left.right.right.space n) :
    (interchangeIso E).hom.map n
      (Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
        (Cell.target E.left.left n x)) =
      Cell.target (coneSquare (comparisonMap E)) n
        (Cell.overlap ((Arrow.rightFunc ⋙ Arrow.rightFunc).mapArrow.mapArrow.obj E) n r s x) :=
  interchange_overlap_target E n r s x

example (n : ℕ) (r s t v : unitInterval)
    (x : E.left.left.left.left.space n) :
    (interchangeIso E).hom.map n
      (Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
        (Cell.overlap E.left.left n t v x)) =
      Cell.overlap (coneSquare (comparisonMap E)) n t v
        (Cell.overlap ((Arrow.leftFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r s x) :=
  interchange_overlap_overlap E n r s t v x

end Topology.LoopPrespectrum.StrictSquare.Double
end
