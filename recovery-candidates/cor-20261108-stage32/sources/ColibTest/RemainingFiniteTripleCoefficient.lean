/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTripleCoefficient

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
    (hv : IsFiniteCorrespondencePoint h i v)
    [LocallyOfFiniteType (correspondenceIntermediateImageTarget f g h z w ≫ h)]
    [LocallyOfFiniteType (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v)) :
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x.1 =
      ∑ᶠ y : {y : genericPoints (correspondenceTripleIncidence f g h i z w v) //
        correspondenceTripleToLeftImageIncidence f g h i z w v y.1 = x.1},
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v y.1.1)
            (correspondenceTripleIncidenceTor f g h i z w v y.1.1 n)).toNat : ℤ)) *
          ((correspondenceTripleToLeftImageIncidence f g h i z w v).residueDegree y.1.1 : ℤ) :=
  correspondenceLeftWeightedRemainingCycle_eq_finsum_tripleTor K f g h i z w v hz hw hv x
