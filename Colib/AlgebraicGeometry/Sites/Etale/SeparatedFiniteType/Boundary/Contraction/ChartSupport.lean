/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.ProjectionExcisionGeometry
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Mono
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Etale.Excision

/-! # Closed support on one actual Cartier cylinder chart

The specified full zero fiber and its retraction are retained after taking the
whole homotopy cylinder. The coefficient comparison uses the original canonical
boundary morphism and actual etale excision on this chart only. No global purity
or retraction on later etale refinements is asserted.
-/

/-! Adapted from `Motivic/Cohomology/A1/Contraction/ChartSupport.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  {E U : SmoothSite (Spec R)} (b : E ⟶ affineLineCylinder.obj X) (d : X ⟶ E)

/-- A specified whole zero fiber has the actual normal-coordinate projection
as retraction, before introducing the homotopy parameter. -/
theorem contractionChart_retraction (hd : d ≫ b = nativeAffineSection R X 0) :
    d ≫ (b ≫ (projection (additiveGroupObject (Spec R))).app X) = 𝟙 X := by
  rw [← Category.assoc, hd, nativeAffineSection_projection]

/-- The retraction is taken in the BASE and then multiplied by the whole line. -/
theorem contractionChartProduct_retraction (hd : d ≫ b = nativeAffineSection R X 0) :
    affineLineCylinder.map d ≫
      affineLineCylinder.map (b ≫ (projection (additiveGroupObject (Spec R))).app X) =
        𝟙 (affineLineCylinder.obj X) := by
  rw [← Functor.map_comp, contractionChart_retraction R X b d hd,
    (affineLineCylinder (S := Spec R)).map_id X]

/-- The complete closed fiber remains Cartesian under the actual product chart. -/
theorem contractionChartProduct_closed_isPullback
    (hd : IsPullback d (𝟙 X) b (nativeAffineSection R X 0)) :
    IsPullback (affineLineCylinder.map d) (𝟙 (affineLineCylinder.obj X))
      (contractionChartProduct R X b) (nativeAffineSection R (affineLineCylinder.obj X) 0) := by
  have h : IsPullback (affineLineCylinder.map d) (𝟙 (affineLineCylinder.obj X))
      (affineLineCylinder.map b) (affineLineCylinder.map (nativeAffineSection R X 0)) := by
    have h' := (parameterProduct (additiveGroupObject (Spec R))).map_isPullback hd
    change IsPullback (affineLineCylinder.map d) (affineLineCylinder.map (𝟙 X))
      (affineLineCylinder.map b) (affineLineCylinder.map (nativeAffineSection R X 0)) at h'
    simpa only [(affineLineCylinder (S := Spec R)).map_id X] using h'
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (productSwapLastIso X (additiveGroupObject (Spec R)) (additiveGroupObject (Spec R))) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    rw [← a1Section_productSwapLast R X 0]
    let T := additiveGroupObject (Spec R)
    change (_ ≫ (productSwapLastIso X T T).hom) ≫ (productSwapLastIso X T T).inv = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem range_fst_of_chart_pullback {P A B C : Scheme.{u}}
    {a : P ⟶ A} {e : P ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback a e f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← h.isoPullback_hom_fst]
  change Set.range ((pullback.fst f g) ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- The original chart product puncture is precisely the complement of its
whole closed fiber. Both squares, rather than a support assumption, supply this. -/
theorem contractionChartProduct_complement [Etale b.left]
    (hd : IsPullback d (𝟙 X) b (nativeAffineSection R X 0))
    (j : U ⟶ E) (q : U ⟶ torusCylinder.obj X)
    (hj : IsPullback q j (openInclusion.app X) b) :
    Set.range (affineLineCylinder.map d).left = (Set.range (affineLineCylinder.map j).left)ᶜ := by
  have hc := (forgetScheme (Spec R)).map_isPullback
    (contractionChartProduct_closed_isPullback R X b d hd)
  change IsPullback (affineLineCylinder.map d).left (𝟙 (affineLineCylinder.obj X).left)
    (contractionChartProduct R X b).left
    (nativeAffineSection R (affineLineCylinder.obj X) 0).left at hc
  have ho := ((forgetScheme (Spec R)).map_isPullback
    (contractionChartPunctureProduct_isPullback R X b j q hj)).flip
  change IsPullback (affineLineCylinder.map j).left (contractionChartPunctureProduct R X q).left
    (contractionChartProduct R X b).left (openInclusion.app (affineLineCylinder.obj X)).left at ho
  rw [range_fst_of_chart_pullback hc, range_fst_of_chart_pullback ho,
    range_nativeAffineSection_zero, Set.preimage_compl]

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  {E U : SmoothSite (Spec (.of k))}
  (b : E ⟶ affineLineCylinder.obj X) [Etale b.left]
  (F : SheafWithTransfers.{u + 1} k) (j : U ⟶ E)
  (q : U ⟶ torusCylinder.obj X)
  (hj : IsPullback q j (openInclusion.app X) b)
  (d : X ⟶ E) (hd : d ≫ b = nativeAffineSection (.of k) X 0)
  (hF : F.obj.IsA1Invariant)

/-- The actual canonical contraction map followed by etale excision on the
specified chart. Its only remaining input is that canonical map's epimorphy. -/
def contractionChartBoundaryIso (hE : Epi (contractionToBoundary X F hF)) :
    (restrict X AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)) ≅
      boundaryCokernel ((SheafWithTransfers.toSheaf k).obj F) j d := by
  let := hE
  let := contractionToBoundary_mono X F hF
  let : IsIso (contractionToBoundary X F hF) := isIso_of_mono_of_epi _
  exact asIso (contractionToBoundary X F hF) ≪≫
    eqToIso (congrArg (boundaryCokernel ((SheafWithTransfers.toSheaf k).obj F)
      (openInclusion.app X)) hd.symm) ≪≫
    boundaryEtaleExcisionIso ((SheafWithTransfers.toSheaf k).obj F)
      (openInclusion.app X) b j q hj d

/-- On the whole homotopy cylinder the fixed closed coefficient is identified
using the canonical boundary map on that cylinder, not current-degree HI. -/
def contractionChartProductBoundaryIso
    (hE : Epi (contractionToBoundary (affineLineCylinder.obj X) F hF)) :
    (restrict (affineLineCylinder.obj X) AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)) ≅
      boundaryCokernel ((SheafWithTransfers.toSheaf k).obj F)
        (affineLineCylinder.map j) (affineLineCylinder.map d) :=
  contractionChartBoundaryIso (affineLineCylinder.obj X)
    (SmoothSite.contractionChartProduct (.of k) X b) F (affineLineCylinder.map j)
    (SmoothSite.contractionChartPunctureProduct (.of k) X q)
    (SmoothSite.contractionChartPunctureProduct_isPullback (.of k) X b j q hj)
    (affineLineCylinder.map d) (SmoothSite.contractionChartProduct_zero (.of k) X b hd)
    hF hE

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
