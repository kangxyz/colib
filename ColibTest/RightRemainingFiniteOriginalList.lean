/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteOriginalList

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x) :
    correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x) =
      correspondenceSixfoldFirstMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) := by
  exact correspondenceRightRemainingTriple_middle_point_eq
    f g h i z w v x y hy

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRightRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRightRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y))) :
    let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    let e := (pullback g g).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x y hy))
    (fun j => correspondenceRightRemainingFiniteOriginalStalkMap f g h i z w v x q
      (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x)
        (correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x (e.inv (s j))))) =
      (fun j => ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq hρ)).hom
          (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v y
            ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
              (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j)))) := by
  exact correspondenceRightRemainingFiniteOriginalStalkMap_originalList
    f g h i z w v x q hq y hy hρ s

end Stacks.Chow
