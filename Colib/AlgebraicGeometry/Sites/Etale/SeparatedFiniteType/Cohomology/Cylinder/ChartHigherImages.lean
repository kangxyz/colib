/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.ContractionBoundary
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.ChartSupport
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.OpenSupport
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.CoefficientIso
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.EtaleExcision

/-! # Actual higher open images from explicit original coefficient inputs

The original PST local-zero and canonical-boundary Epi families remain inputs.
The specified positive-degree HI is used only below the target strict degree.
Actual product-chart excision and marked detection retain the original maps.
-/

/-! Adapted from `Motivic/Cohomology/A1/Contraction/ChartHigherImageInputs.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.Stacks.Cohomology.FreeYonedaUnivLE
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k]
  (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
  (hEpi : OriginalPresheaf.CanonicalBoundaryEpi k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (X : SmoothSite (Spec (.of k))) {E U : SmoothSite (Spec (.of k))}
  (b : E ⟶ affineLineCylinder.obj X) [Etale b.left]
  (F : SheafWithTransfers.{u + 1} k) (j : U ⟶ E)
  (q : U ⟶ torusCylinder.obj X)
  (hj : IsPullback q j (openInclusion.app X) b)
  (d : X ⟶ E) (hd : IsPullback d (𝟙 X) b (nativeAffineSection (.of k) X 0))

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "X₁" => affineLineCylinder.obj X
local notation "d₁" => affineLineCylinder.map d
local notation "j₁" => affineLineCylinder.map j
local notation "b₁" => SmoothSite.contractionChartProduct (CommRingCat.of k) X b
local notation "q₁" => SmoothSite.contractionChartPunctureProduct (CommRingCat.of k) X q

include hD hEpi hj hd in
/-- The actual chart boundary of the original ordinary presheaf is zero in the
specified HI degree. The original-presheaf canonical Epi is the explicit input family. -/
private theorem chartProduct_originalBoundary_isZero_succ (m : ℕ)
    (hP : (SheafCohomology.withTransfers k F (m + 1)).IsA1Invariant) :
    IsZero ((inverseImage (d₁).left).obj (presheafBoundaryAmbient
      (cohomologyPresheaf.{u + 1, u + 1} G (m + 1)) j₁)) := by
  let PT := (PresheafWithTransfers.toPresheaf k).obj
    (SheafCohomology.withTransfers k F (m + 1))
  have hdz : d ≫ b = nativeAffineSection (.of k) X 0 := by
    simpa only [Category.id_comp] using hd.w
  have hzero := SmoothSite.contractionChartProduct_zero (.of k) X b hdz
  have hModel : IsZero (presheafBoundary PT (openInclusion.app X₁)
      (d₁ ≫ b₁)) := by
    rw [hzero]
    exact SheafCohomology.isZero_zeroSectionBoundary_succ_of_coefficient_inputs
      hD hEpi F m hP X₁
  have hChart := hModel.of_iso
    (presheafBoundaryEtaleExcisionIso PT (openInclusion.app X₁)
      b₁ j₁ q₁ (SmoothSite.contractionChartPunctureProduct_isPullback
        (.of k) X b j q hj) d₁).symm
  exact hChart.of_iso ((inverseImage (d₁).left).mapIso
    (presheafBoundaryAmbientCoefficientIso
      (SheafCohomology.withTransfersGraphIso k F (m + 1)) j₁)).symm

include hD hEpi hj hd in
/-- The actual product-chart open direct image vanishes in each specified
positive HI degree. In the target-degree proof this is used only below that degree. -/
theorem chartProduct_higherDirectImage_isZero_succ (m : ℕ)
    (hP : (SheafCohomology.withTransfers k F (m + 1)).IsA1Invariant) :
    IsZero (((directImage (j₁).left).rightDerived (m + 1)).obj
      ((restrict (affineLineCylinder.obj U) AddCommGrpCat).obj G)) := by
  have hclosed := (SmoothSite.forgetScheme (Spec (.of k))).map_isPullback
    (SmoothSite.contractionChartProduct_closed_isPullback (.of k) X b d hd)
  change IsPullback (d₁).left (𝟙 (X₁).left) (b₁).left
    (nativeAffineSection (.of k) X₁ 0).left at hclosed
  let : IsClosedImmersion (d₁).left :=
    MorphismProperty.of_isPullback hclosed.flip inferInstance
  have hopen := (SmoothSite.forgetScheme (Spec (.of k))).map_isPullback
    (SmoothSite.contractionChartPunctureProduct_isPullback (.of k) X b j q hj)
  change IsPullback (q₁).left (j₁).left (openInclusion.app X₁).left
    (b₁).left at hopen
  let : IsOpenImmersion (j₁).left :=
    MorphismProperty.of_isPullback hopen inferInstance
  exact higherDirectImage_isZero_of_positiveBoundary_zero (.of k) j₁ (d₁).left
    (SmoothSite.contractionChartProduct_complement (.of k) X b d hd j q hj) G m
    (chartProduct_originalBoundary_isZero_succ hD hEpi X b F j q hj d hd m hP)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
