/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleCombinedColumnEuler

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
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let firstStageMap := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
    let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      ambientPoint
    let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      ambientPoint
    let firstMiddleRing := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g
      h i ambientPoint)
    let secondMiddleRing := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f
      g h i ambientPoint)
    let firstMiddleMap := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap ambientPoint).hom
    let secondMiddleMap := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      ambientPoint).hom
    ∃ (t : List firstMiddleRing) (s : List secondMiddleRing) (ht : IsRegular firstMiddleRing t)
      (hs : IsRegular secondMiddleRing s)
      (hY : firstIdeal = Ideal.ofList (t.map firstMiddleMap)) (hZ : secondIdeal = Ideal.ofList
        (s.map secondMiddleMap)),
      let t' := t.map firstMiddleMap
      let s' := s.map secondMiddleMap
      let ht' := (correspondenceOriginalMiddleLists_regular_append f g h i
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1) t s ht hs hY hZ).1
      (∑ b : Fin (t'.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler (fun j => firstStageMap (s'.get j))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t' ht' hY b)) =
        ∑ᶠ a : ℕ, (-1 : ℤ) ^ a *
          ((Module.length ambientRing (correspondenceTripleIncidenceTor f g h i z w v x.1
            a)).toNat : ℤ) :=
  exists_correspondenceOriginalMiddleLists_remainingEuler_eq_combinedTor k f g h i z w v x
