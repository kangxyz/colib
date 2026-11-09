/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteImageLabels

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceRightImageIncidence f g h i z w v) (p : PrimeSpectrum
      (correspondenceRightRemainingImageStalk f g h i z w v x)) :
    let E := correspondenceRightIntermediateSupportProduct f g h i z w v
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let L := correspondenceRightRemainingOriginalGenericLabels f g h i z w v x
    {η : L // correspondenceRightRemainingOriginalImagePrime f g h i z w v x η = p} ≃
      {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p}  := by
  exact correspondenceRightRemainingOriginalImagePrimeFiberEquiv
    f g h i z w v x p

end Stacks.Chow
