/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.ActualPairColumnCombinedEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence Stacks.Chow
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let supportPoint := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x.1
    let pairProjection := (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) :
      correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶ correspondenceIncidence f g h z
        w)
    let pairAmbientPoint := correspondenceIncidenceAmbientInclusion f g h z w (pairProjection
      supportPoint)
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let pairMiddleRing := (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      pairAmbientPoint)
    let secondMiddleRing := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f
      g h i ambientPoint)
    let pairAmbientMap := correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x.1
    let pairMiddleMap := ((correspondenceMiddlePair f g h).stalkMap pairAmbientPoint).hom
    let secondMiddleMap := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      ambientPoint).hom
    let firstStageMap := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
    ∀ {r m : ℕ} (t : Fin r → pairMiddleRing) (ht : IsRegular pairMiddleRing (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h pairAmbientPoint) = Ideal.span (Set.range t))
    (s : Fin m → secondMiddleRing) (_hs : IsRegular secondMiddleRing (List.ofFn s))
    (_hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceSixfoldSecondMiddlePair f g h i ambientPoint) = Ideal.span (Set.range s)),
    let l := List.ofFn (fun j => pairAmbientMap (pairMiddleMap (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x.1 t ht hkt
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      Koszul.seqEuler (fun j => firstStageMap (secondMiddleMap (s j)))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 l hreg.1 hreg.2 n)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length ambientRing (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat
          : ℤ) :=
  finsum_actualPair_remainingFirstEuler_eq_combinedTor k f g h i z w v x
