/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.GeometricImage
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-! # Actual small-site packaging of geometric boundary refinements -/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/GeometricRefinement.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `84f658ad2d10c6e4caf0b5fe3beefa38025e262f`. All generator and image-sieve maps use the
actual native Laurent cylinder and closed inverse-image boundary.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (V : EtaleSeparatedFiniteType X.left) (E : SmoothSite (Spec (.of k)))
  (q : E ⟶ SmoothSite.Contraction.affineLineCylinder.obj ((toSmoothSite X).obj V)) [Etale q.left]

/-- The actual geometric source, with its original composite cylinder map. -/
def geometricRefinementNeighborhood :
    EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left :=
  MorphismProperty.Over.mk ⊤ (q.left ≫ ((cylinderNeighborhood X).obj V).hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-- The corrected ambient source maps to the literal cylinder over V. -/
def geometricRefinementToCylinder :
    geometricRefinementNeighborhood X V E q ⟶ (cylinderNeighborhood X).obj V :=
  MorphismProperty.Over.homMk q.left rfl

/-- Forgetting the small-site wrapper changes neither the scheme nor its field map. -/
def geometricRefinementIso : E ≅
    (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj
      (geometricRefinementNeighborhood X V E q) := by
  have hC : ((cylinderNeighborhood X).obj V).hom ≫
      (SmoothSite.Contraction.affineLineCylinder.obj X).hom =
      (SmoothSite.Contraction.affineLineCylinder.obj ((toSmoothSite X).obj V)).hom :=
    MorphismProperty.Over.w (SmoothSite.Contraction.affineLineCylinder.map (toBase X V))
  exact MorphismProperty.Over.isoMk (Iso.refl E.left) (by
    change 𝟙 E.left ≫ ((q.left ≫ ((cylinderNeighborhood X).obj V).hom) ≫
      (SmoothSite.Contraction.affineLineCylinder.obj X).hom) = E.hom
    rw [Category.id_comp, Category.assoc, hC]
    exact MorphismProperty.Over.w q)

variable {W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left}
  (e : E ⟶ (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj W)
  (he : e.left ≫ W.hom = q.left ≫ ((cylinderNeighborhood X).obj V).hom)

/-- The actual original ambient map, regarded as a small-site refinement. -/
def geometricRefinementToOriginal : geometricRefinementNeighborhood X V E q ⟶ W :=
  MorphismProperty.Over.homMk e.left he

/-- The identity-underlying comparison retains the original ambient arrow. -/
theorem geometricRefinementIso_toOriginal :
    (geometricRefinementIso X V E q).hom ≫
      (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).map
        (geometricRefinementToOriginal X V E q e he) = e := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 E.left ≫ e.left = e.left
  exact Category.id_comp _

/-- The identity-underlying comparison also retains the original cylinder arrow. -/
theorem geometricRefinementIso_toCylinder :
    (geometricRefinementIso X V E q).hom ≫
      (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).map
        (geometricRefinementToCylinder X V E q) ≫
      (parameterProductUnderlyingIso X
        (SmoothSite.additiveGroupObject (Spec (.of k)))).hom.app V = q := by
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 E.left ≫ q.left ≫ 𝟙 _ = q.left
  rw [Category.id_comp, Category.comp_id]

/-- The image-sieve arrow is exactly the supplied original base-open arrow once
both original whole-zero maps agree. No closed-point-cover shortcut is used. -/
theorem geometricRefinement_zero_arrow
    (z : V.left ⟶ E.left)
    (hz : z ≫ q.left =
      (SmoothSite.Contraction.nativeAffineSection (.of k) ((toSmoothSite X).obj V) 0).left)
    (v : V ⟶ (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W)
    (hv : z ≫ e.left = v.left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left) :
    geometricZeroLift X V (geometricRefinementToCylinder X V E q) z hz ≫
      (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).map
        (geometricRefinementToOriginal X V E q e he) = v := by
  let W' := geometricRefinementNeighborhood X V E q
  let f := geometricRefinementToOriginal X V E q e he
  let g := geometricZeroLift X V (geometricRefinementToCylinder X V E q) z hz
  have hf₁ :
      ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).map f).left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left =
      pullback.fst W'.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left ≫ e.left :=
    pullback.lift_fst _ _ _
  have hf₂ :
      ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).map f).left ≫
      pullback.snd W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left =
      pullback.snd W'.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left :=
    pullback.lift_snd _ _ _
  have hg₁ : g.left ≫ pullback.fst W'.hom
      (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left = z := pullback.lift_fst _ _ _
  have hg₂ : g.left ≫ pullback.snd W'.hom
      (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left = V.hom :=
    pullback.lift_snd _ _ _
  have hv₂ : v.left ≫ pullback.snd W.hom
      (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left = V.hom :=
    MorphismProperty.Over.w v
  apply MorphismProperty.Over.Hom.ext
  change g.left ≫
    ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).map f).left = v.left
  apply pullback.hom_ext
  · rw [Category.assoc, hf₁, ← Category.assoc, hg₁, hv]
  · rw [Category.assoc, hf₂, hg₂, hv₂]

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
