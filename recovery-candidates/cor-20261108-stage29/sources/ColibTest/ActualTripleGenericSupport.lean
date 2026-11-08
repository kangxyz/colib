/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericSupport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example (x : correspondenceTripleIncidence f g h i z w v) :
    Module.Finite (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x) :=
  finite_correspondenceTripleIncidenceSupportStalkModule f g h i z w v x

example [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    (correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v x.1).radical =
      IsLocalRing.maximalIdeal (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1) :=
  radical_correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v x

example [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    Module.support (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x.1) ∩
      Module.support (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1) ∩
      Module.support (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x.1) ⊆
          {IsLocalRing.closedPoint
            (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)} :=
  support_correspondenceTripleIncidence_threeModules f g h i z w v x

section Field

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example (x : correspondenceTripleIncidence f g h i z w v) :
    IsRegularLocalRing (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :=
  isRegularLocalRing_correspondenceSixfoldAmbient_stalk k f g h i
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x)

example (x : correspondenceTripleIncidence f g h i z w v) :
    ringKrullDim (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) =
      (correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x : WithBot ℕ∞) :=
  ringKrullDim_eq_correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x

end Field

end Stacks.Chow
