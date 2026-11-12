/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.Normalization.Compactification.IntegralChart
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import Colib.AlgebraicGeometry.Normalization.Compactification.NormalIntegralSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite

/-!
# Normal finite covers retaining the original finite chart

Normalize a Nagata compact target in the original normal integral source. A finite map from
that source to an open chart gives an open immersion into this actual normalization. Its
image is the entire inverse image of the chart, not merely a dense open part of it.

This uses the pinned native relative-normalization and Nagata finiteness theorems directly.
The chart argument adapts `Normalization/Compactification/FiniteChart/CompactificationChart.lean`
from the Motivic source checkpoint dated 2026-10-21. Unlike its generically étale construction,
Nagata finiteness needs no auxiliary separability assumption. No smoothness of the compact
cover is asserted. Choosing the finite coordinates and a relative-curve smooth open remains
a separate presentation problem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- An open immersion is an isomorphism above the image of an original open. -/
theorem isIso_restrict_open_image {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    [IsOpenImmersion j] (U : Y.Opens) : IsIso (j ∣_ j ''ᵁ U) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  obtain ⟨y, hy, he⟩ := x.property
  have hmem : y ∈ j ⁻¹ᵁ (j ''ᵁ U) := ⟨y, hy, rfl⟩
  refine ⟨⟨y, hmem⟩, ?_⟩
  apply Subtype.ext
  exact (morphismRestrict_base_coe j _ ⟨y, hmem⟩).trans he

/-- The original finite map stays finite over the image of its chart. -/
theorem finite_comp_restrict_open_image {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (j : Y ⟶ Z) [IsOpenImmersion j] (U : Y.Opens) [IsFinite (f ∣_ U)] :
    IsFinite ((f ≫ j) ∣_ j ''ᵁ U) := by
  have : IsIso (j ∣_ j ''ᵁ U) := isIso_restrict_open_image j U
  have : IsFinite (f ∣_ j ⁻¹ᵁ (j ''ᵁ U)) := by
    rw [j.preimage_image_eq]
    infer_instance
  rw [morphismRestrict_comp]
  infer_instance

/-- The Cartesian chart used by relative normalization is finite. -/
theorem finite_comp_pullback_open_image {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (j : Y ⟶ Z) [IsOpenImmersion j] (U : Y.Opens) [IsFinite (f ∣_ U)] :
    IsFinite (pullback.snd (f ≫ j) (j ''ᵁ U).ι) := by
  have := finite_comp_restrict_open_image f j U
  rw [← (isPullback_morphismRestrict (f ≫ j) (j ''ᵁ U)).flip.isoPullback_inv_snd]
  infer_instance

/-- A finite map to an open chart of a Nagata target extends to a normal finite cover,
retaining the original normal integral scheme as the entire inverse image of that chart. -/
@[colib_tag "COL-1064"]
theorem exists_normal_finite_cover_of_nagata_finite_chart
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsNormal X] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) [IsFinite f] (j : Y ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (hZ : IsNagataScheme Z) :
    ∃ (N : Scheme.{u}) (i : X ⟶ N) (π : N ⟶ Z),
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧
      IsOpenImmersion i ∧ IsFinite π ∧ i ≫ π = f ≫ j ∧
      Set.range i = π ⁻¹' Set.range j := by
  let g := f ≫ j
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsFinite g.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType g hZ
  have : IsNormal g.normalization := g.isNormal_normalization_of_integral_source
  have : IsOpenImmersion g.toNormalization := inferInstance
  refine ⟨g.normalization, g.toNormalization, g.fromNormalization, inferInstance,
    LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization, inferInstance,
    inferInstance, inferInstance, g.toNormalization_fromNormalization, ?_⟩
  have := finite_comp_pullback_open_image f j ⊤
  have htop : g ⁻¹ᵁ (j ''ᵁ ⊤) = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨f x, trivial, rfl⟩
  simpa only [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange] using
    g.range_toNormalization_eq_preimage_integral_chart (j ''ᵁ ⊤) htop

end AlgebraicGeometry.Scheme
