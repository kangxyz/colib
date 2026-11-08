/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteOriginalList

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- The actual closed fibre and actual projection equalities suffice. No abstract ring
-- comparison, regularity, genericity, field hypothesis, or connectedness is supplied.
example (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y))) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let e := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))
    (fun j => correspondenceRemainingFiniteOriginalStalkMap f g h i z w v x q
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x)
        (correspondenceRemainingImageMiddleStalkMap f g h i z w v x (e.inv (s j))))) =
      (fun j => ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
        (Inseparable.of_eq hρ)).hom
          (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
            ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
              (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j)))) :=
  correspondenceRemainingFiniteOriginalStalkMap_originalList f g h i z w v x q hq y hy hρ s
