/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
# An actual splitting stratum of a Nisnevich cover

Take a generic point of the reduced closed subscheme defined by the given
closed set. A field-valued lift spreads to a section over an open neighborhood
in that subscheme. Its complement is a strictly smaller closed subset of the
original base. The section is retained over the actual restriction of the
reduced closed subscheme to the complementary open of the base.

See [Voevodsky, Lemma 2.15](https://arxiv.org/pdf/0805.4576#page=10).
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Nisnevich

set_option backward.isDefEq.respectTransparency false in
/-- A morphism lifting field-valued points splits over a nonempty open
stratum of every nonempty reduced closed subscheme. -/
theorem exists_splittingStratum {X Y : Scheme.{u}} [IsNoetherian X]
    (f : Y ⟶ X) [LocallyOfFiniteType f]
    (hlift : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X),
      ∃ b : Spec (.of K) ⟶ Y, b ≫ f = a)
    (Z : Closeds X) (hne : Z ≠ ⊥) :
    let z := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
    ∃ C : Closeds X, C < Z ∧
      ∃ s : (z ⁻¹ᵁ C.compl).toScheme ⟶ Y, s ≫ f = (z ⁻¹ᵁ C.compl).ι ≫ z := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let R := I.subscheme
  let z : R ⟶ X := I.subschemeι
  change ∃ C : Closeds X, C < Z ∧
    ∃ s : (z ⁻¹ᵁ C.compl).toScheme ⟶ Y, s ≫ f = (z ⁻¹ᵁ C.compl).ι ≫ z
  have hz : Set.range z = (Z : Set X) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z
  have : IsLocallyNoetherian R := LocallyOfFiniteType.isLocallyNoetherian z
  have : IsReduced R := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Z
  obtain ⟨x, hx⟩ := Closeds.coe_nonempty.mpr hne
  obtain ⟨r, _⟩ := hz.symm.subset hx
  let η : genericPoints R := genericPoints.ofComponent
    ⟨irreducibleComponent r, irreducibleComponent_mem_irreducibleComponents r⟩
  let : Field (R.presheaf.stalk η) :=
    (isField_stalk_of_closure_mem_irreducibleComponents R η η.property).toField
  obtain ⟨a, ha⟩ := hlift (R.presheaf.stalk η) (R.fromSpecStalk η ≫ z)
  obtain ⟨U, hηU, s, _, hs⟩ := spread_out_of_isGermInjective' z f a ha
  let C : Closeds X := ⟨z '' (U : Set R)ᶜ,
    z.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hCZ : C < Z := by
    refine lt_of_le_of_ne ?_ ?_
    · rintro _ ⟨p, _, rfl⟩
      exact hz.subset ⟨p, rfl⟩
    · intro h
      have hm : z η ∈ C := by rw [h]; exact hz.subset ⟨η, rfl⟩
      obtain ⟨p, hp, he⟩ := hm
      exact hp ((z.isClosedEmbedding.injective he).symm ▸ hηU)
  have hU : z ⁻¹ᵁ C.compl = U := by
    ext p
    change z p ∉ z '' (U : Set R)ᶜ ↔ p ∈ U
    constructor
    · intro hp
      by_contra h
      exact hp ⟨p, h, rfl⟩
    · intro hp
      rintro ⟨q, hq, he⟩
      exact hq ((z.isClosedEmbedding.injective he).symm ▸ hp)
  refine ⟨C, hCZ, ?_⟩
  rw [hU]
  exact ⟨s, hs⟩

end AlgebraicGeometry.Nisnevich
