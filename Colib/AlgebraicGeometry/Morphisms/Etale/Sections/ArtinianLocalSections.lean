/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Etale.ArtinianSections
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Prescribed residue points of etale schemes over local Artinian rings

The native formal-smooth lifting theorem supplies the algebra section.
The affine neighborhood and its original residue morphism are retained.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Morphisms/Etale/Sections/HenselianEtaleSections.lean`, blob
`33d8cb017b72ec3ad94c9133c45fb7007ea2e330`.
The source is the actual original scheme or ordinary free-Yoneda Ext group.
All monic quotient fibers retain their full scheme structure.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom.ArtinianLocal
open _root_.Algebra.Etale.Artinian

private theorem exists_section_of_etale_of_exists_lift
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hlift : ∀ (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B]
      (φ : B →ₐ[R] ResidueField R), ∃ ψ : B →ₐ[R] R,
        (IsScalarTower.toAlgHom R R (ResidueField R)).comp ψ = φ)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (_root_.IsLocalRing.residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (_root_.IsLocalRing.residue R)) ≫ t = s := by
  obtain ⟨B, j, hj, hmem, _⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := s default) (U := ⊤) (by simp)
  let := hj
  have hrange : Set.range s ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x default]
  let s' := IsOpenImmersion.lift j s hrange
  have hs' : s' ≫ j = s := IsOpenImmersion.lift_fac j s hrange
  let a := Spec.preimage (j ≫ f)
  have ha : a.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp (by
    simpa only [a, Spec.map_preimage] using inferInstanceAs (Etale (j ≫ f)))
  let : Algebra R B := a.hom.toAlgebra
  let : Algebra.Etale R B := ha
  have hφ : a ≫ Spec.preimage s' = CommRingCat.ofHom (_root_.IsLocalRing.residue R) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, a, Spec.map_preimage, ← Category.assoc, hs'] using hs
  let φ : B →ₐ[R] ResidueField R :=
    { (Spec.preimage s').hom with commutes' := fun r ↦ congr($hφ r) }
  obtain ⟨ψ, hψ⟩ := hlift B φ
  have hψa : a ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 (CommRingCat.of R) := by
    ext r
    exact ψ.commutes r
  have hres : CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom (_root_.IsLocalRing.residue R) =
      Spec.preimage s' := by
    ext b
    exact DFunLike.congr_fun hψ b
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← Spec.map_preimage (j ≫ f), ← Spec.map_comp, hψa, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hres, Spec.map_preimage, hs']

/-- A residue-field point of any étale scheme over a local Artinian ring lifts
to a section with the given reduction. The base ring need not be reduced. -/
theorem exists_section_of_etale_of_artinian {R : Type u} [CommRing R]
    [IsLocalRing R] [IsArtinianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (s : Spec (.of (ResidueField R)) ⟶ X)
    (hs : s ≫ f = Spec.map (CommRingCat.ofHom (_root_.IsLocalRing.residue R))) :
    ∃ t : Spec (.of R) ⟶ X,
      t ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (_root_.IsLocalRing.residue R)) ≫ t = s :=
  exists_section_of_etale_of_exists_lift
    (fun _ _ _ _ ↦ exists_lift_of_etale) f s hs

end AlgebraicGeometry.Scheme.Hom.ArtinianLocal
