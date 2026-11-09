/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingGenericPushPull

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

open Classical in
example
    [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫
      pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫
      pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (t : correspondenceIncidence g h i w v) (p : genericPoints
      (correspondenceRightIntermediateImageProduct f g h i z w v)) (hp :
      (correspondenceRightImageExteriorProjection f g h i z w v) p.1 =
      ((correspondenceIncidenceMap g h i w v).toImage) t) :
    let C := fieldChowSituation K
    let E := correspondenceRightIntermediateSupportProduct f g h i z w v
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let π := correspondenceRightExteriorProjection f g h i z w v
    let π' := correspondenceRightImageExteriorProjection f g h i z w v
    let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
    let sI := q ≫ sJ
    let sT := π' ≫ sJ
    letI := isFinite_correspondenceIncidenceToImage g h i w v hw hv
    letI := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
    ((q).residueDegree t : ℤ) * flatPullbackWeight C sT π'
      (relativeDimension (C).dimensionFunction sI t +
        (correspondenceFirstSupportDimension K f g z : ℤ)) p.1 =
      ∑ᶠ η : {η : genericPoints E // q' η.1 = p.1},
        if π η.1.1 = t then
          (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
            ((q').residueDegree η.1.1 : ℤ)
        else 0  := by
  exact correspondenceRightImage_fixedLabel_genericPushPull
    K f g h i z w v hw hv t p hp

end Stacks.Chow
