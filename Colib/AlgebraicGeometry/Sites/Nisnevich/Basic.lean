/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.CompletelyDecomposed
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# The big Nisnevich site

The covering families are étale and completely decomposed. For small indexed families,
the second condition is exactly Stacks' `IsCompletelyDecomposedFamily`, not a second
residue-field model. General presieves can have large collections of arrows; choosing
one lift per target point reduces their base-change theorem to the native Stacks theorem.

This file constructs the actual pretopology and Grothendieck topology on schemes, proves
the Zariski–Nisnevich–étale inclusions, and splits covers over field spectra. No separable
closedness or perfection condition is imposed on these fields. The construction uses
Mathlib's native `Precoverage`; it is not a topology on a replacement scheme category.

Implementation adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/Basic.lean`
and `FieldLifting.lean` at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380.
The native completely-decomposed predicate and base-change theorem carry Stacks tags
0GTI and 0GTK; these citations concern those inputs, not a claim that they state the
entire Nisnevich site construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Nisnevich

/-- Étale presieves lifting every point with an unchanged residue field. -/
@[colib_tag "COL-0302", colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/Basic.lean:34-107"
  "adaptation" "Etale completely decomposed covers, using the native Stacks family condition",
  colib_ref "MVW2006" "Lecture 12, p. 89, opening definition" "generalization"
  "Etale residue-field lifting covers, extended from schemes over a field to all schemes"]
def precoverage : Precoverage Scheme.{u} where
  coverings X := {R | (∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), R f → Etale f) ∧
    ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧
      ∃ y : Y, f y = x ∧ IsIso (f.residueFieldMap y)}

/-- The point-and-residue-field characterization of a Nisnevich presieve. -/
theorem mem_precoverage_iff {X : Scheme.{u}} {R : Presieve X} :
    R ∈ precoverage X ↔ (∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), R f → Etale f) ∧
      ∀ x : X, ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧
        ∃ y : Y, f y = x ∧ IsIso (f.residueFieldMap y) := Iff.rfl

/-- The criterion for an arbitrarily indexed family, without a smallness hypothesis. -/
theorem ofArrows_mem_precoverage_iff {X : Scheme.{u}} {ι : Type v}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ precoverage X ↔
      (∀ i, Etale (f i)) ∧
        ∀ x : X, ∃ (i : ι) (y : Y i), f i y = x ∧ IsIso ((f i).residueFieldMap y) := by
  rw [mem_precoverage_iff]
  constructor
  · rintro ⟨he, hl⟩
    refine ⟨fun i ↦ he _ ⟨i⟩, fun x ↦ ?_⟩
    obtain ⟨_, _, ⟨i⟩, y, hy, hi⟩ := hl x
    exact ⟨i, y, hy, hi⟩
  · rintro ⟨he, hl⟩
    refine ⟨fun {_} _ ⟨i⟩ ↦ he i, fun x ↦ ?_⟩
    obtain ⟨i, y, hy, hi⟩ := hl x
    exact ⟨Y i, f i, ⟨i⟩, y, hy, hi⟩

/-- Small indexed Nisnevich families use precisely the native completely decomposed condition. -/
@[colib_tag "COL-0302"]
theorem ofArrows_mem_precoverage_iff_isCompletelyDecomposedFamily
    {X : Scheme.{u}} {ι : Type v} [Small.{u} ι]
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ precoverage X ↔
      (∀ i, Etale (f i)) ∧ IsCompletelyDecomposedFamily f := by
  rw [ofArrows_mem_precoverage_iff, isCompletelyDecomposedFamily_iff]

instance : precoverage.{u}.HasIsos where
  mem_coverings_of_isIso f _ := by
    rw [mem_precoverage_iff]
    refine ⟨fun {_} _ h ↦ ?_, fun x ↦ ?_⟩
    · cases h
      infer_instance
    · refine ⟨_, f, Presieve.singleton_self f, inv f x, ?_, inferInstance⟩
      exact congrArg (fun g ↦ g x) (IsIso.inv_hom_id f)

instance : precoverage.{u}.IsStableUnderComposition where
  comp_mem_coverings {ι} {X} {Y} f hf {σ} {Z} g hg := by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    simp only [ofArrows_mem_precoverage_iff] at hg
    refine ⟨fun ij ↦ ?_, fun x ↦ ?_⟩
    · have := hf.1 ij.1
      have := (hg ij.1).1 ij.2
      infer_instance
    · obtain ⟨i, y, rfl, hfy⟩ := hf.2 x
      obtain ⟨j, z, rfl, hgz⟩ := (hg i).2 y
      refine ⟨⟨i, j⟩, z, Scheme.Hom.comp_apply _ _ _, ?_⟩
      rw [Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' hfy hgz

instance : precoverage.{u}.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} {X} {Y} f hf {T} g {P} p₁ p₂ h := by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    refine ⟨fun i ↦ ?_, fun t ↦ ?_⟩
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Etale) (h i).flip (hf.1 i)
    · choose i y hy hi using hf.2
      have hc : IsCompletelyDecomposedFamily (fun x : X ↦ f (i x)) :=
        (isCompletelyDecomposedFamily_iff _).2 fun x ↦ ⟨x, y x, hy x, hi x⟩
      obtain ⟨x, z, hz, hres⟩ := (isCompletelyDecomposedFamily_iff _).1
        (isCompletelyDecomposedFamily_pullback (fun x : X ↦ f (i x)) g hc) t
      let e := (h (i x)).flip.isoPullback
      have he : e.inv ≫ p₁ (i x) = pullback.snd (f (i x)) g :=
        (h (i x)).flip.isoPullback_inv_snd
      refine ⟨i x, e.inv z, ?_, ?_⟩
      · exact (congrArg (fun a ↦ a z) he).trans hz
      · have hcomp : IsIso ((e.inv ≫ p₁ (i x)).residueFieldMap z) := by
          rw [he]
          exact hres
        exact IsIso.of_isIso_fac_right (hh := hcomp)
          (Scheme.residueFieldMap_comp e.inv (p₁ (i x)) z).symm

/-- The big Nisnevich pretopology on the native category of schemes. -/
@[colib_tag "COL-0302"]
def pretopology : Pretopology Scheme.{u} := precoverage.toPretopology

/-- The big Nisnevich Grothendieck topology. -/
@[colib_tag "COL-0302", colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/Basic.lean:73-76"
  "adaptation" "The Grothendieck topology generated by Nisnevich covering families"]
def topology : GrothendieckTopology Scheme.{u} := precoverage.toGrothendieck

/-- Covering sieves contain a family with the displayed Nisnevich lifting property. -/
theorem mem_topology_iff_contains_cover {X : Scheme.{u}} {R : Sieve X} :
    R ∈ topology X ↔ ∃ Q ∈ precoverage X, Q ≤ R :=
  Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition

/-- The displayed pretopology generates the big Nisnevich topology. -/
theorem pretopology_toGrothendieck : pretopology.{u}.toGrothendieck = topology :=
  Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck

/-- Every Zariski covering family is a Nisnevich covering family. -/
theorem zariskiPrecoverage_le_precoverage : Scheme.zariskiPrecoverage.{u} ≤ precoverage := by
  intro X R hR
  rw [mem_precoverage_iff]
  refine ⟨fun {_} f hf ↦ ?_, fun x ↦ ?_⟩
  · have : IsOpenImmersion f := hR.2 hf
    infer_instance
  · obtain ⟨Y, f, hf, y, hy⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff Scheme.forget).mp hR.1 x
    have : IsOpenImmersion f := hR.2 hf
    exact ⟨Y, f, hf, y, hy, inferInstance⟩

/-- Nisnevich covering families are étale covering families. -/
theorem precoverage_le_etalePrecoverage : precoverage.{u} ≤ Scheme.etalePrecoverage := by
  intro X R hR
  refine ⟨?_, fun {_ _} hf ↦ hR.1 _ hf⟩
  rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff]
  intro x
  obtain ⟨Y, f, hf, y, hy, _⟩ := hR.2 x
  exact ⟨Y, f, hf, y, hy⟩

/-- The Zariski topology is coarser than the Nisnevich topology. -/
@[colib_tag "COL-0302"]
theorem zariskiTopology_le_topology : Scheme.zariskiTopology.{u} ≤ topology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_precoverage

/-- The Nisnevich topology is coarser than the étale topology. -/
@[colib_tag "COL-0302"]
theorem topology_le_etaleTopology : topology.{u} ≤ Scheme.etaleTopology :=
  Precoverage.toGrothendieck_mono precoverage_le_etalePrecoverage

set_option backward.isDefEq.respectTransparency.types false in
/-- A Nisnevich family lifts every field-valued point, not just separably closed points. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/FieldLifting.lean:87-98"
  "adaptation" "A residue-field-isomorphism lift lifts any field-valued point"]
theorem exists_lift_of_mem_precoverage {X : Scheme.{u}} {R : Presieve X}
    (hR : R ∈ precoverage X) (K : Type u) [Field K] (x : Spec (.of K) ⟶ X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧
      ∃ y : Spec (.of K) ⟶ Y, y ≫ f = x := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective x
  obtain ⟨Y, f, hf, y, rfl, hi⟩ := hR.2 x
  let := hi
  refine ⟨Y, f, hf, Spec.map (inv (f.residueFieldMap y) ≫ a) ≫
    Y.fromSpecResidueField y, ?_⟩
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField y,
    ← Spec.map_comp_assoc]
  simp [Scheme.SpecToEquivOfField]

/-- A covering family of a field spectrum contains a morphism with a section. -/
@[colib_tag "COL-0302", colib_ref "MVW2006" "Lecture 12, p. 89, Example 12.2" "generalization"
  "A Nisnevich cover of a field spectrum splits, in the big site with arbitrary index types"]
theorem exists_section_of_mem_precoverage (K : Type u) [Field K]
    {R : Presieve (Spec (.of K))} (hR : R ∈ precoverage _) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of K)), R f ∧
      ∃ s : Spec (.of K) ⟶ Y, s ≫ f = 𝟙 _ :=
  exists_lift_of_mem_precoverage hR K (𝟙 _)

/-- Every Nisnevich covering sieve at a field spectrum is maximal. -/
@[colib_tag "COL-0302", colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/Basic.lean:139-156"
  "adaptation" "Covering sieves at a field spectrum are maximal, for arbitrary fields"]
theorem covering_sieve_eq_top (K : Type u) [Field K]
    {R : Sieve (Spec (.of K))} (hR : R ∈ topology _) : R = ⊤ := by
  obtain ⟨Q, hQ, hQR⟩ := mem_topology_iff_contains_cover.mp hR
  obtain ⟨Y, f, hf, s, hs⟩ := exists_section_of_mem_precoverage K hQ
  apply Sieve.id_mem_iff_eq_top.mp
  simpa only [hs] using R.downward_closed (hQR _ _ hf) s

/-- The only Nisnevich covering sieve at a field spectrum is the maximal sieve. -/
theorem mem_topology_iff (K : Type u) [Field K] (R : Sieve (Spec (.of K))) :
    R ∈ topology _ ↔ R = ⊤ := by
  constructor
  · exact covering_sieve_eq_top K
  · rintro rfl
    exact topology.top_mem _

/-- Every field defines an actual point of the big Nisnevich topos by its functor of points. -/
@[colib_tag "COL-0302"]
def fieldPoint (K : Type u) [Field K] : topology.Point where
  fiber := coyoneda.obj ⟨Spec (.of K)⟩
  jointly_surjective R hR x := by
    obtain ⟨Q, hQ, hQR⟩ := mem_topology_iff_contains_cover.mp hR
    obtain ⟨Y, f, hf, y, hy⟩ := exists_lift_of_mem_precoverage hQ K x
    exact ⟨Y, f, hQR _ _ hf, y, hy⟩

end AlgebraicGeometry.Nisnevich
