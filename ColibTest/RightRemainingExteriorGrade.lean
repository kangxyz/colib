/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingExteriorGrade

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
    [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫
      pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫
      pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (η : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    let C := fieldChowSituation K
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let π := correspondenceRightExteriorProjection f g h i z w v
    let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
    let sI := q ≫ sJ
    let sE := π ≫ sI
    relativeDimension (C).dimensionFunction sE η.1 =
      relativeDimension (C).dimensionFunction sI (π η.1) +
        (correspondenceFirstSupportDimension K f g z : ℤ)  := by
  exact relativeDimension_correspondenceRightExterior_generic
    K f g h i z w v hw hv η

end Stacks.Chow
