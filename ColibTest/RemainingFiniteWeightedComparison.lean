/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteWeightedComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence Stacks.Chow Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

example
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))
    (hv : IsFiniteCorrespondencePoint h i v)
    [LocallyOfFiniteType (correspondenceIntermediateImageTarget f g h z w ≫ h)] [LocallyOfFiniteType
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    {r : ℕ} (s : Fin r → ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z
        w v (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)))) (hsr : IsRegular
        ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v (correspondenceLeftImageIncidenceInclusion f
          g h i z w v x.1)) = Ideal.span (Set.range s)) :
    let R := correspondenceRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    letI := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x.1 =
      ∑ᶠ q : MaximalSpectrum B,
        (∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
          Koszul.seqEuler
            (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
              (algebraMap R B (α (s j))))
            (Localization.AtPrime q.asIdeal ⊗[B] M b)) *
              (Module.finiteAlgebraResidueDegree R B q : ℤ) :=
  correspondenceLeftWeightedRemainingCycle_eq_finsum_maximalEuler K f g h i z w v hz hw x hv s hsr
    hs
