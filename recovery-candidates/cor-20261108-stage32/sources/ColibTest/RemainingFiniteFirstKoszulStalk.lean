/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteFirstKoszulStalk

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow
open Stacks.ModuleStalkSpecialization

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- The coefficient is the actual finite Tor-sheaf stalk in the original degree.
example
    [Flat f] [Flat h] [Flat i] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
    (ht : IsRegular _ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))) =
        Ideal.span (Set.range t)) (n : ℕ) :
    let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
    let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk a
    let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v a)
    let l := List.ofFn (fun j => correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y
      ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y t ht hkt
    let := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v y l hreg.1 hreg.2 n
    let := correspondenceRemainingFiniteTorStalkFirstStageModule f g h i z w v x q y hρ n
    ((correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) ≃ₗ[P]
      (Koszul.seqComplexTensor l.get
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v y)).homology n :=
  correspondenceRemainingFiniteFirstKoszulStalkLinearEquiv f g h i z w v x q y hρ t ht hkt n

-- The source action is the actual finite-algebra germ of the unchanged original Z-list.
example
    [Flat f] [Flat h] [Flat i] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
    (ht : IsRegular _ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))) =
        Ideal.span (Set.range t)) (n : ℕ) {sLen : ℕ}
    (s : Fin sLen → (pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y)))
    (j : Fin sLen)
    (u : (correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let := stalkModule (correspondenceRemainingFiniteTorSheaf f g h i z w v x n) q
    let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
    let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v a)
    let l := List.ofFn (fun j => correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y
      ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y t ht hkt
    let := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v y l hreg.1 hreg.2 n
    let eZ := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))
    let e := correspondenceRemainingFiniteFirstKoszulStalkLinearEquiv
      f g h i z w v x q y hρ t ht hkt n
    e ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x)
        (correspondenceRemainingImageMiddleStalkMap f g h i z w v x (eZ.inv (s j)))) • u) =
      correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
        ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
          (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j)) • e u :=
  correspondenceRemainingFiniteFirstKoszulStalkLinearEquiv_originalList_smul
    f g h i z w v x q hq y hy hρ t ht hkt n s j u
