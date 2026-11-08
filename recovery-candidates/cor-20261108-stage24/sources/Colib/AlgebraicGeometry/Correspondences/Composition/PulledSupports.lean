/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.Embedding
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Full pulled supports in the actual triple product

The left and right supports are the native ideal-sheaf comaps along the two
projections of the actual triple product. Their inclusions are literally
`Scheme.IdealSheafData.subschemeι`. In particular, these constructions do not
replace a pulled closed subscheme by its reduction.

The actual incidence maps to these subschemes through the native pullback
universal property and `Scheme.IdealSheafData.comapIso`. The equations below
identify the original incidence inclusion and both original support projections.
The incidence is their scheme-theoretic intersection, and its kernel is their
ideal-sheaf sum, with no radical taken.
All schemes and structure morphisms are arbitrary; no field, connectedness,
normality, finite-type, or nonemptiness hypothesis is imposed here.

Implementation provenance: `kangxyz/motivic` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/GlobalAmbientTorComparison.lean`.
This lower geometric interface was reconstructed from retained consumers. It is
not a byte-for-byte restoration of that file or a claim to recover its Tor
comparison. The mathematical background is the scheme-theoretic fibre-product
construction used in MVW2006, Lecture 1, composition preceding Proposition 1.7.
The actual comap/fibre-product comparison is reused from the pinned Mathlib
`AlgebraicGeometry/IdealSheaf/Functorial.lean`, not reproved in a parallel model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The full inverse-image ideal of the left integral support in the triple product. -/
def correspondenceLeftPulledIdeal (z : pullback (C := Scheme) f g) :
    (correspondenceTripleProduct f g h).IdealSheafData :=
  (integralComponentAt z).comap (pullback.fst (pullback.snd f g) (pullback.fst g h))

/-- The full inverse-image ideal of the right integral support in the triple product. -/
def correspondenceRightPulledIdeal (w : pullback (C := Scheme) g h) :
    (correspondenceTripleProduct f g h).IdealSheafData :=
  (integralComponentAt w).comap (pullback.snd (pullback.snd f g) (pullback.fst g h))

/-- The native closed immersion of the full left pulled subscheme. -/
def correspondenceLeftPulledInclusion (z : pullback (C := Scheme) f g) :
    (correspondenceLeftPulledIdeal f g h z).subscheme ⟶
      correspondenceTripleProduct f g h :=
  (correspondenceLeftPulledIdeal f g h z).subschemeι

/-- The native closed immersion of the full right pulled subscheme. -/
def correspondenceRightPulledInclusion (w : pullback (C := Scheme) g h) :
    (correspondenceRightPulledIdeal f g h w).subscheme ⟶
      correspondenceTripleProduct f g h :=
  (correspondenceRightPulledIdeal f g h w).subschemeι

instance isClosedImmersion_correspondenceLeftPulledInclusion
    (z : pullback (C := Scheme) f g) :
    IsClosedImmersion (correspondenceLeftPulledInclusion f g h z) := by
  dsimp [correspondenceLeftPulledInclusion]
  infer_instance

instance isClosedImmersion_correspondenceRightPulledInclusion
    (w : pullback (C := Scheme) g h) :
    IsClosedImmersion (correspondenceRightPulledInclusion f g h w) := by
  dsimp [correspondenceRightPulledInclusion]
  infer_instance

/-- The left pulled subscheme projects to the original integral support by native base change. -/
def correspondenceLeftPulledProjection (z : pullback (C := Scheme) f g) :
    (correspondenceLeftPulledIdeal f g h z).subscheme ⟶ (integralComponentAt z).subscheme :=
  ((integralComponentAt z).comapIso
    (pullback.fst (pullback.snd f g) (pullback.fst g h))).hom ≫ pullback.snd _ _

/-- The right pulled subscheme projects to the original integral support by native base change. -/
def correspondenceRightPulledProjection (w : pullback (C := Scheme) g h) :
    (correspondenceRightPulledIdeal f g h w).subscheme ⟶ (integralComponentAt w).subscheme :=
  ((integralComponentAt w).comapIso
    (pullback.snd (pullback.snd f g) (pullback.fst g h))).hom ≫ pullback.snd _ _

/-- The left pulled support is the actual cartesian inverse image of its integral support. -/
theorem isPullback_correspondenceLeftPulled (z : pullback (C := Scheme) f g) :
    IsPullback (correspondenceLeftPulledInclusion f g h z)
      (correspondenceLeftPulledProjection f g h z)
      (pullback.fst (pullback.snd f g) (pullback.fst g h))
      (integralComponentAt z).subschemeι := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    ((integralComponentAt z).comapIso
      (pullback.fst (pullback.snd f g) (pullback.fst g h))) ?_ rfl
  · simp only [correspondenceLeftPulledProjection, Category.assoc,
      ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
    rfl
  · exact Scheme.IdealSheafData.comapIso_hom_fst _ _

/-- The right pulled support is the actual cartesian inverse image of its integral support. -/
theorem isPullback_correspondenceRightPulled (w : pullback (C := Scheme) g h) :
    IsPullback (correspondenceRightPulledInclusion f g h w)
      (correspondenceRightPulledProjection f g h w)
      (pullback.snd (pullback.snd f g) (pullback.fst g h))
      (integralComponentAt w).subschemeι := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    ((integralComponentAt w).comapIso
      (pullback.snd (pullback.snd f g) (pullback.fst g h))) ?_ rfl
  · simp only [correspondenceRightPulledProjection, Category.assoc,
      ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
    rfl
  · exact Scheme.IdealSheafData.comapIso_hom_fst _ _

variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The actual incidence lifts to the full left pulled subscheme. -/
def correspondenceIncidenceToLeftPulled :
    correspondenceIncidence f g h z w ⟶ (correspondenceLeftPulledIdeal f g h z).subscheme :=
  pullback.lift (correspondenceIncidenceInclusion f g h z w) (pullback.fst _ _)
    (correspondenceIncidenceInclusion_fst f g h z w) ≫
      ((integralComponentAt z).comapIso
        (pullback.fst (pullback.snd f g) (pullback.fst g h))).inv

/-- The actual incidence lifts to the full right pulled subscheme. -/
def correspondenceIncidenceToRightPulled :
    correspondenceIncidence f g h z w ⟶ (correspondenceRightPulledIdeal f g h w).subscheme :=
  pullback.lift (correspondenceIncidenceInclusion f g h z w) (pullback.snd _ _)
    (correspondenceIncidenceInclusion_snd f g h z w) ≫
      ((integralComponentAt w).comapIso
        (pullback.snd (pullback.snd f g) (pullback.fst g h))).inv

/-- The left lift preserves the original scheme-theoretic incidence inclusion. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceToLeftPulled_inclusion :
    correspondenceIncidenceToLeftPulled f g h z w ≫
      correspondenceLeftPulledInclusion f g h z =
        correspondenceIncidenceInclusion f g h z w := by
  simp [correspondenceIncidenceToLeftPulled, correspondenceLeftPulledInclusion,
    correspondenceLeftPulledIdeal]

/-- The right lift preserves the original scheme-theoretic incidence inclusion. -/
@[reassoc (attr := simp)]
theorem correspondenceIncidenceToRightPulled_inclusion :
    correspondenceIncidenceToRightPulled f g h z w ≫
      correspondenceRightPulledInclusion f g h w =
        correspondenceIncidenceInclusion f g h z w := by
  simp [correspondenceIncidenceToRightPulled, correspondenceRightPulledInclusion,
    correspondenceRightPulledIdeal]

/-- The actual incidence is the scheme-theoretic intersection of the full pulled supports.
The square preserves both literal inclusions into the actual triple product. -/
theorem isPullback_correspondencePulledIncidence :
    IsPullback (correspondenceIncidenceToLeftPulled f g h z w)
      (correspondenceIncidenceToRightPulled f g h z w)
      (correspondenceLeftPulledInclusion f g h z)
      (correspondenceRightPulledInclusion f g h w) := by
  have hL : correspondenceIncidenceToLeftPulled f g h z w ≫
      correspondenceLeftPulledProjection f g h z = pullback.fst _ _ := by
    simp only [correspondenceIncidenceToLeftPulled, correspondenceLeftPulledProjection,
      Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]
  have hR : correspondenceIncidenceToRightPulled f g h z w ≫
      correspondenceRightPulledProjection f g h w = pullback.snd _ _ := by
    simp only [correspondenceIncidenceToRightPulled, correspondenceRightPulledProjection,
      Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]
  have Hright : IsPullback (correspondenceRightPulledProjection f g h w)
      (correspondenceRightPulledInclusion f g h w ≫
        pullback.fst (pullback.snd f g) (pullback.fst g h))
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h) (pullback.snd f g) :=
    (isPullback_correspondenceRightPulled f g h w).flip.paste_vert
      (IsPullback.of_hasPullback (pullback.snd f g) (pullback.fst g h)).flip
  have Houter : IsPullback
      (correspondenceIncidenceToRightPulled f g h z w ≫
        correspondenceRightPulledProjection f g h w) (pullback.fst _ _)
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g) := by
    rw [hR]
    exact (IsPullback.of_hasPullback
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
      ((integralComponentAt w).subschemeι ≫ pullback.fst g h)).flip
  have Hrestricted : IsPullback (correspondenceIncidenceToRightPulled f g h z w)
      (pullback.fst _ _)
      (correspondenceRightPulledInclusion f g h w ≫
        pullback.fst (pullback.snd f g) (pullback.fst g h))
      (integralComponentAt z).subschemeι :=
    Houter.of_right (by simp only [← Category.assoc,
      correspondenceIncidenceToRightPulled_inclusion, correspondenceIncidenceInclusion_fst])
      Hright
  have Htotal : IsPullback
      (correspondenceIncidenceToLeftPulled f g h z w ≫
        correspondenceLeftPulledProjection f g h z)
      (correspondenceIncidenceToRightPulled f g h z w) (integralComponentAt z).subschemeι
      (correspondenceRightPulledInclusion f g h w ≫
        pullback.fst (pullback.snd f g) (pullback.fst g h)) := by
    rw [hL]
    exact Hrestricted.flip
  exact Htotal.of_right (by simp) (isPullback_correspondenceLeftPulled f g h z).flip

/-- The incidence ideal is the sum of the two full pulled ideals, with no radical taken.
This follows from the native ideal-sheaf inclusion and kernel universal properties. -/
theorem correspondenceIncidenceInclusion_ker :
    (correspondenceIncidenceInclusion f g h z w).ker =
      correspondenceLeftPulledIdeal f g h z ⊔ correspondenceRightPulledIdeal f g h w := by
  apply le_antisymm
  · let J := correspondenceLeftPulledIdeal f g h z ⊔ correspondenceRightPulledIdeal f g h w
    let qL : J.subscheme ⟶ (correspondenceLeftPulledIdeal f g h z).subscheme :=
      Scheme.IdealSheafData.inclusion le_sup_left
    let qR : J.subscheme ⟶ (correspondenceRightPulledIdeal f g h w).subscheme :=
      Scheme.IdealSheafData.inclusion le_sup_right
    have hq : qL ≫ correspondenceLeftPulledInclusion f g h z =
        qR ≫ correspondenceRightPulledInclusion f g h w := by
      simp [qL, qR, correspondenceLeftPulledInclusion, correspondenceRightPulledInclusion]
    let H := isPullback_correspondencePulledIncidence f g h z w
    let k := H.lift qL qR hq
    have hk : k ≫ correspondenceIncidenceInclusion f g h z w = J.subschemeι := by
      rw [← correspondenceIncidenceToLeftPulled_inclusion f g h z w, ← Category.assoc]
      simp [k, qL, correspondenceLeftPulledInclusion]
    calc
      (correspondenceIncidenceInclusion f g h z w).ker ≤
          (k ≫ correspondenceIncidenceInclusion f g h z w).ker :=
        Scheme.Hom.le_ker_comp _ _
      _ = J := by rw [hk, Scheme.IdealSheafData.ker_subschemeι]
  · apply sup_le
    · have H := Scheme.Hom.le_ker_comp (correspondenceIncidenceToLeftPulled f g h z w)
        (correspondenceLeftPulledInclusion f g h z)
      rw [correspondenceIncidenceToLeftPulled_inclusion] at H
      simpa only [correspondenceLeftPulledInclusion,
        Scheme.IdealSheafData.ker_subschemeι] using H
    · have H := Scheme.Hom.le_ker_comp (correspondenceIncidenceToRightPulled f g h z w)
        (correspondenceRightPulledInclusion f g h w)
      rw [correspondenceIncidenceToRightPulled_inclusion] at H
      simpa only [correspondenceRightPulledInclusion,
        Scheme.IdealSheafData.ker_subschemeι] using H

end Stacks.Chow
