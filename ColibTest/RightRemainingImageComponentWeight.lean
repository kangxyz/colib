/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageComponentWeight

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫
      pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫
      pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p})
      (hp : (IdealSheafData.stalk (correspondenceRightRemainingImageComponent f g h i z w v t)
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) ≤ p.1.asIdeal) :
    let C := fieldChowSituation K
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let π' := correspondenceRightImageExteriorProjection f g h i z w v
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
    let sT := π' ≫ sJ
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    ((Module.length (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl
        (correspondenceRightRemainingImageComponentStalk f g h i z w v x t))).toNat : ℤ) =
      flatPullbackWeight C sT π'
        (relativeDimension (C).dimensionFunction (q ≫ sJ) t +
          (correspondenceFirstSupportDimension K f g z : ℤ)) ((T).fromSpecStalk x₀ p.1)  := by
  exact length_correspondenceRightRemainingImageComponentStalk_eq_originalGradeWeight
    K f g h i z w v x t hw hv p hp

end Stacks.Chow
