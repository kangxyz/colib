/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.ProjectionExcisionGeometry
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.RestrictionMono
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.ContractionDensity

/-!
# The coefficient restriction on an actual product chart

Adapted from `Motivic/Cohomology/A1/Cartier/Restriction/H1RestrictionInputs.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

/-- Integral-affine local vanishing detects the literal chart product restriction. -/
theorem chartProduct_restrictionToDirectImage_mono
    {k : Type u} [Field k] (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    (X : SmoothSite (Spec (.of k))) {E U : SmoothSite (Spec (.of k))}
    (b : E ⟶ affineLineCylinder.obj X) [Etale b.left]
    (F : SheafWithTransfers.{u + 1} k) (j : U ⟶ E) (q : U ⟶ torusCylinder.obj X)
    (hj : IsPullback q j (openInclusion.app X) b) (hF : F.obj.IsA1Invariant) :
    Mono (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F)
      (affineLineCylinder.map j)) := by
  let b₁ := SmoothSite.contractionChartProduct (.of k) X b
  let q₁ := SmoothSite.contractionChartPunctureProduct (.of k) X q
  let j₁ := affineLineCylinder.map j
  have hj₁ := SmoothSite.contractionChartPunctureProduct_isPullback (.of k) X b j q hj
  let : IsOpenImmersion j₁.left := MorphismProperty.of_isPullback
    ((SmoothSite.forgetScheme (Spec (.of k))).map_isPullback hj₁)
    (inferInstanceAs (IsOpenImmersion (openInclusion.app (affineLineCylinder.obj X)).left))
  exact restrictionToDirectImage_mono_of_dense_of_integralAffineLocalZero hD j₁ F hF
    (chartOpen_denseRange (.of k) (affineLineCylinder.obj X) b₁ j₁ q₁ hj₁)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
