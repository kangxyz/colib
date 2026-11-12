/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Normalization.Compactification.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Full finite boundary of the literal fixed-target normalization

The finite chart controls the entire complement of the original source, not
only the generic fibre. Only the newly added infinity is given reduced scheme
structure. No prescribed marked scheme is reduced or replaced.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification.FixedTarget

variable {Y C G W : Scheme.{u}} (g : Y ⟶ C) [QuasiCompact g] [QuasiSeparated g]

/-- A genuinely finite chart has no new points in the relative normalization.
This is the native normalization/smooth-base-change isomorphism, not a generic
function-field compactification. -/
theorem preimage_chart_subset_source (i : G ⟶ C) [IsOpenImmersion i]
    (v : W ⟶ Y) (r : W ⟶ G) [IsFinite r] (H : IsPullback v r g i) :
    g.fromNormalization ⁻¹' Set.range i ⊆ Set.range g.toNormalization := by
  have : IsFinite (pullback.snd g i) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have : IsIso (pullback.snd g i).toNormalization := inferInstance
  intro c hc
  obtain ⟨b, hb⟩ := hc
  obtain ⟨a, ha, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback g.fromNormalization i) c b hb.symm
  obtain ⟨w, hw⟩ :=
    ((pullback.snd g i).toNormalization ≫ g.normalizationPullback i).surjective a
  refine ⟨pullback.fst g i w, ?_⟩
  have he := congrArg (fun f => f w) (g.toNormalization_normalizationPullback_fst i)
  exact he.symm.trans ((congrArg (pullback.fst g.fromNormalization i) hw).trans ha)

variable [IsOpenImmersion g.toNormalization]

/-- The reduced closed complement of the entire original source. -/
def infinityIdeal : g.normalization.IdealSheafData :=
  IdealSheafData.vanishingIdeal
    ⟨(Set.range g.toNormalization)ᶜ,
      g.toNormalization.isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- The new infinity, not a replacement for any original marking. -/
abbrev infinity : Scheme.{u} := (infinityIdeal g).subscheme

/-- The literal closed inclusion of the new infinity. -/
abbrev infinityInclusion : infinity g ⟶ g.normalization := (infinityIdeal g).subschemeι

instance : IsClosedImmersion (infinityInclusion g) := by
  dsimp [infinityInclusion]
  infer_instance

@[simp] theorem range_infinityInclusion :
    Set.range (infinityInclusion g) = (Set.range g.toNormalization)ᶜ := by
  rw [infinityInclusion, IdealSheafData.range_subschemeι]
  simp [infinityIdeal]

theorem source_disjoint_infinity :
    Disjoint (Set.range g.toNormalization) (Set.range (infinityInclusion g)) := by
  rw [range_infinityInclusion]
  exact disjoint_compl_right

/-- A finite original chart and a whole finite bad-boundary cover force the
entire new infinity to be finite over the unchanged base. -/
theorem finite_infinity {S D : Scheme.{u}} (π : C ⟶ S) [IsProper π]
    [IsFinite g.fromNormalization] (i : G ⟶ C) [IsOpenImmersion i]
    (v : W ⟶ Y) (r : W ⟶ G) [IsFinite r] (H : IsPullback v r g i)
    (d : D ⟶ C) [IsFinite (d ≫ π)]
    (hbad : (Set.range i)ᶜ ⊆ Set.range d) :
    IsFinite (infinityInclusion g ≫ g.fromNormalization ≫ π) := by
  have hsupport : ∀ b : infinity g, g.fromNormalization (infinityInclusion g b) ∈
      Set.range d := by
    intro b
    apply hbad
    intro hb
    have hsource := preimage_chart_subset_source g i v r H hb
    have hinf : infinityInclusion g b ∈ Set.range (infinityInclusion g) := ⟨b, rfl⟩
    rw [range_infinityInclusion] at hinf
    exact hinf hsource
  have : LocallyQuasiFinite (infinityInclusion g ≫ g.fromNormalization ≫ π) := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro s
    have hfin := g.fromNormalization.finite_preimage
      (((d ≫ π).finite_preimage_singleton s).image d)
    have hpre := Set.Finite.preimage
      (infinityInclusion g).isClosedEmbedding.injective.injOn hfin
    apply hpre.subset
    intro b hb
    obtain ⟨a, ha⟩ := hsupport b
    refine ⟨a, ?_, ha⟩
    change π (d a) = s
    rw [ha]
    exact hb
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- A finite marked scheme embeds closedly in the compactification, retaining
its entire scheme structure. The argument uses properness and immersion. -/
theorem marked_isClosedImmersion {S Z : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (s : Z ⟶ Y) [IsClosedImmersion s] [IsFinite (s ≫ g ≫ π)] :
    IsClosedImmersion (s ≫ g.toNormalization) := by
  have : IsProper ((s ≫ g.toNormalization) ≫ (g.fromNormalization ≫ π)) := by
    simpa only [Category.assoc, g.toNormalization_fromNormalization_assoc] using
      (inferInstance : IsProper (s ≫ g ≫ π))
  have : IsProper (s ≫ g.toNormalization) :=
    IsProper.of_comp (s ≫ g.toNormalization) (g.fromNormalization ≫ π)
  exact IsClosedImmersion.of_isPreimmersion _
    (s ≫ g.toNormalization).isClosedMap.isClosed_range

end AlgebraicGeometry.Scheme.EtaleCompactification.FixedTarget
