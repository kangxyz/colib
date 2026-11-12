/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.GraphProduct

/-!
# The full boundary of the original finite product

An inverse boundary remains Cartesian in the second factor of the original
relative product. The entire marked section is the open component of its
full inverse boundary, through the original maps.

Adapted from
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Boundary/SectionPairGraphMarkedNorm.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S B X Z : Scheme.{u}} (b : B ⟶ S) (q : X ⟶ S) (q' : Z ⟶ S)
  (v : Z ⟶ X) (hv : q' = v ≫ q)

/-- Change the second factor using the actual structure equation. -/
def productSecondMap : pullback b q' ⟶ pullback b q :=
  (pullback.congrHom rfl hv).hom ≫ retainedProductInclusion b q v

@[reassoc (attr := simp)]
theorem productSecondMap_fst :
    productSecondMap b q q' v hv ≫ pullback.fst b q = pullback.fst b q' := by
  subst q'
  simp [productSecondMap]

@[reassoc (attr := simp)]
theorem productSecondMap_snd :
    productSecondMap b q q' v hv ≫ pullback.snd b q = pullback.snd b q' ≫ v := by
  subst q'
  simp [productSecondMap]

/-- Changing the second factor is the actual base change of that map. -/
theorem productSecondMap_isPullback :
    IsPullback (pullback.snd b q') (productSecondMap b q q' v hv) v (pullback.snd b q) := by
  subst q'
  simpa [productSecondMap] using retainedProductInclusion_isPullback b q v

section Boundary

variable {P C Y E : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P)
  (d : E ⟶ C) (z : Z ⟶ P) (e : E ⟶ Z) (H : IsPullback d e f z)

/-- The product comparison for the original full inverse boundary. -/
abbrev productInverseBoundaryToTarget :
    pullback b (d ≫ f ≫ π) ⟶ pullback b (z ≫ π) :=
  productSecondMap b (z ≫ π) (d ≫ f ≫ π) e (by
    rw [← Category.assoc, H.w, Category.assoc])

/-- The entire inverse boundary product is Cartesian under the original finite
map in the second factor. -/
theorem productInverseBoundary_isPullback :
    IsPullback (retainedProductInclusion b (f ≫ π) d)
      (productInverseBoundaryToTarget b π f d z e H)
      (retainedProductInclusion b π f) (retainedProductInclusion b π z) := by
  have houter := (retainedProductInclusion_isPullback b (f ≫ π) d).flip.paste_vert H
  have houter' : IsPullback (retainedProductInclusion b (f ≫ π) d)
      (productInverseBoundaryToTarget b π f d z e H ≫ pullback.snd b (z ≫ π))
      (retainedProductInclusion b π f ≫ pullback.snd b π) z := by
    simpa only [productInverseBoundaryToTarget, productSecondMap_snd,
      retainedProductInclusion_snd] using houter
  refine houter'.of_bot ?_ (retainedProductInclusion_isPullback b π z).flip
  apply pullback.hom_ext
  · simp only [Category.assoc, retainedProductInclusion_fst,
      productInverseBoundaryToTarget, productSecondMap_fst]
  · simp only [Category.assoc, retainedProductInclusion_snd, retainedProductInclusion_snd_assoc,
      productInverseBoundaryToTarget, productSecondMap_snd_assoc, ← H.w]

variable (j : Y ⟶ C) (s : Z ⟶ Y) (Hs : IsPullback s (𝟙 Z) (j ≫ f) z)

/-- The original marked section over the actual whole parameter product. -/
abbrev productMarkedSection : pullback b (z ≫ π) ⟶ pullback b (j ≫ f ≫ π) :=
  productSecondMap b (j ≫ f ≫ π) (z ≫ π) s (by
    have h : s ≫ j ≫ f = z := by simpa only [Category.id_comp] using Hs.w
    simpa only [Category.assoc] using (congrArg (fun g ↦ g ≫ π) h).symm)

/-- The marked square still identifies precisely the retained component of
the full inverse boundary product. -/
theorem productMarkedSection_isPullback :
    IsPullback (productMarkedSection b π f z j s Hs) (𝟙 _)
      (retainedProductInclusion b (f ≫ π) j ≫ retainedProductInclusion b π f)
      (retainedProductInclusion b π z) := by
  have houter := (productSecondMap_isPullback b (j ≫ f ≫ π) (z ≫ π) s
    (by
      have h : s ≫ j ≫ f = z := by simpa only [Category.id_comp] using Hs.w
      simpa only [Category.assoc] using (congrArg (fun g ↦ g ≫ π) h).symm)).flip.paste_vert Hs
  have houter' : IsPullback (productMarkedSection b π f z j s Hs)
      ((𝟙 _) ≫ pullback.snd b (z ≫ π))
      ((retainedProductInclusion b (f ≫ π) j ≫ retainedProductInclusion b π f) ≫
        pullback.snd b π) z := by
    simpa only [Category.comp_id, Category.id_comp, Category.assoc,
      retainedProductInclusion_snd, retainedProductInclusion_snd_assoc,
      productMarkedSection] using houter
  refine houter'.of_bot ?_ (retainedProductInclusion_isPullback b π z).flip
  have h : s ≫ j ≫ f = z := by simpa only [Category.id_comp] using Hs.w
  apply pullback.hom_ext <;>
    simp [Category.assoc, productMarkedSection, h]

end Boundary

end AlgebraicGeometry.Scheme.RelativeCurvePencil
