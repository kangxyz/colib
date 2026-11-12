/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Naturality
public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Zero
import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic

/-!
# Finite zero schemes of products of sections

The whole zero scheme of a product retains the product ideal, with the
actual zero schemes of the factors mapping into it. Finiteness of both
factor cuts gives finiteness of the product cut over an affine projection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

open AffineLineFiber

variable {k : Type u} [Field k] {P : Scheme.{u}} (b : P ⟶ Spec (.of k))

local notation "Z₀(" s ")" => fiber (sectionToAffineLine b s) 0
local notation "i₀(" s ")" => inclusion (sectionToAffineLine b s) 0

/-- A morphism on which the section vanishes factors through its actual zero scheme. -/
def sectionZeroLift (s : Γ(P, ⊤)) {D : Scheme.{u}} (a : D ⟶ P)
    (ha : a.appTop s = 0) : D ⟶ Z₀(s) :=
  pullback.lift (a ≫ b) a (by
    rw [← sectionToAffineLine_comp a b, ha, sectionToAffineLine_zero])

@[reassoc (attr := simp)] theorem sectionZeroLift_inclusion (s : Γ(P, ⊤))
    {D : Scheme.{u}} (a : D ⟶ P) (ha : a.appTop s = 0) :
    sectionZeroLift b s a ha ≫ i₀(s) = a :=
  pullback.lift_snd _ _ _

/-- Divisibility of two equations gives an inclusion of their whole zero schemes. -/
def sectionZeroInclusionOfDvd (s t : Γ(P, ⊤)) (h : s ∣ t) : Z₀(s) ⟶ Z₀(t) :=
  sectionZeroLift b t (i₀(s)) (by
    obtain ⟨r, rfl⟩ := h
    rw [map_mul, section_zero_inclusion_appTop, zero_mul])

@[reassoc (attr := simp)] theorem sectionZeroInclusionOfDvd_inclusion
    (s t : Γ(P, ⊤)) (h : s ∣ t) : sectionZeroInclusionOfDvd b s t h ≫ i₀(t) = i₀(s) :=
  sectionZeroLift_inclusion ..

instance sectionZeroInclusionOfDvd_isClosedImmersion (s t : Γ(P, ⊤)) (h : s ∣ t) :
    IsClosedImmersion (sectionZeroInclusionOfDvd b s t h) := by
  let a := sectionZeroInclusionOfDvd b s t h
  have : IsClosedImmersion (a ≫ i₀(t)) := by
    rw [show a ≫ i₀(t) = i₀(s) from sectionZeroInclusionOfDvd_inclusion b s t h]
    infer_instance
  exact IsClosedImmersion.of_comp a (i₀(t))

/-- The actual zero scheme of the product is defined by the product ideal. -/
theorem sectionZero_ker_mul (s t : Γ(P, ⊤)) :
    (i₀(s * t)).ker = (i₀(s)).ker * (i₀(t)).ker := by
  apply IdealSheafData.eq_of_stalk_eq
  intro x
  rw [IdealSheafData.stalk_mul]
  simp only [inclusion_stalk, sectionToAffineLine_zero_scalar, map_mul,
    Ideal.span_singleton_mul_span_singleton]

private theorem support_ker_eq_range {D E : Scheme.{u}} (i : D ⟶ E) [IsClosedImmersion i] :
    (i.ker.support : Set E) = Set.range i := by
  rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]

/-- If both factor cuts are finite over an affine locally finite-type
projection, then their product cut is finite over that projection. -/
theorem isFinite_sectionZero_mul {X : Scheme.{u}} (p : P ⟶ X)
    [IsAffineHom p] [LocallyOfFiniteType p] (s t : Γ(P, ⊤))
    [IsFinite (i₀(s) ≫ p)] [IsFinite (i₀(t) ≫ p)] : IsFinite (i₀(s * t) ≫ p) := by
  let a := sectionZeroInclusionOfDvd b s (s * t) ⟨t, rfl⟩
  let c := sectionZeroInclusionOfDvd b t (s * t) ⟨s, mul_comm s t⟩
  have ha : a ≫ i₀(s * t) = i₀(s) := sectionZeroInclusionOfDvd_inclusion ..
  have hc : c ≫ i₀(s * t) = i₀(t) := sectionZeroInclusionOfDvd_inclusion ..
  have hr : Set.range (i₀(s * t)) = Set.range (i₀(s)) ∪ Set.range (i₀(t)) := by
    simp only [← support_ker_eq_range (i₀(s * t)), ← support_ker_eq_range (i₀(s)),
      ← support_ker_eq_range (i₀(t)), sectionZero_ker_mul, IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup]
  let m := coprod.desc a c
  let : Surjective m := ⟨fun y => by
    have hy : (i₀(s * t)) y ∈ Set.range (i₀(s)) ∪ Set.range (i₀(t)) :=
      hr ▸ ⟨y, rfl⟩
    rcases hy with ⟨x, hx⟩ | ⟨x, hx⟩
    · use (coprod.inl : Z₀(s) ⟶ _) x
      apply (i₀(s * t)).isClosedEmbedding.injective
      change ((coprod.inl ≫ m) ≫ i₀(s * t)) x = _
      simpa only [m, coprod.inl_desc, ha] using hx
    · use (coprod.inr : Z₀(t) ⟶ _) x
      apply (i₀(s * t)).isClosedEmbedding.injective
      change ((coprod.inr ≫ m) ≫ i₀(s * t)) x = _
      simpa only [m, coprod.inr_desc, hc] using hx⟩
  have hm : m ≫ i₀(s * t) ≫ p = coprod.desc (i₀(s) ≫ p) (i₀(t) ≫ p) := by
    change coprod.desc a c ≫ i₀(s * t) ≫ p = _
    rw [coprod.desc_comp]
    simp only [← Category.assoc, ha, hc]
  let : IsFinite (m ≫ i₀(s * t) ≫ p) := hm.symm ▸ inferInstance
  have hUC : UniversallyClosed (i₀(s * t) ≫ p) :=
    UniversallyClosed.of_comp_surjective m _
  have hI : IsIntegralHom (i₀(s * t) ≫ p) :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hUC, inferInstance⟩
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨hI, inferInstance⟩

end AlgebraicGeometry.Scheme
