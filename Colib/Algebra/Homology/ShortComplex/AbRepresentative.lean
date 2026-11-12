/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Representatives for homology of abelian groups

The abstract homology of an abelian-group short complex is represented by
elements of the kernel of its second arrow. The vanishing criterion and
functoriality use the actual homology quotient and its cycles isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ShortComplex

variable (S : ShortComplex AddCommGrpCat.{u})

/-- The class of an element killed by the second arrow in the native homology. -/
def abHomologyClass (x : S.X₂) (hx : S.g x = 0) : S.homology :=
  S.homologyπ (S.abCyclesIso.inv ⟨x, hx⟩)

private theorem abHomologyIso_hom_class (x : S.X₂) (hx : S.g x = 0) :
    S.abHomologyIso.hom (S.abHomologyClass x hx) =
      QuotientAddGroup.mk (⟨x, hx⟩ : S.g.hom.ker) := by
  have h := ConcreteCategory.congr_hom
    S.abLeftHomologyData.homologyπ_comp_homologyIso_hom (S.abCyclesIso.inv ⟨x, hx⟩)
  change S.abHomologyIso.hom (S.abHomologyClass x hx) =
    QuotientAddGroup.mk (S.abCyclesIso.hom (S.abCyclesIso.inv ⟨x, hx⟩)) at h
  simpa only [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply] using h

/-- The class vanishes exactly when the representative is the image of the first arrow. -/
theorem abHomologyClass_eq_zero_iff (x : S.X₂) (hx : S.g x = 0) :
    S.abHomologyClass x hx = 0 ↔ ∃ y : S.X₁, S.f y = x := by
  rw [← (ConcreteCategory.bijective_of_isIso S.abHomologyIso.hom).1.eq_iff,
    map_zero, abHomologyIso_hom_class, QuotientAddGroup.eq_zero_iff,
    AddMonoidHom.mem_range]
  exact exists_congr (fun y => Subtype.ext_iff)

/-- Every native homology element has a cycle representative. -/
theorem exists_abHomologyClass (z : S.homology) :
    ∃ (x : S.X₂) (hx : S.g x = 0), S.abHomologyClass x hx = z := by
  obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).1 inferInstance z
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso S.abCyclesIso.inv).2 y
  exact ⟨x.val, x.property, (congrArg S.homologyπ hx).trans hy⟩

/-- The native class is additive on cycle representatives. -/
theorem abHomologyClass_sub (x y : S.X₂) (hx : S.g x = 0) (hy : S.g y = 0) :
    S.abHomologyClass (x - y) (by rw [map_sub, hx, hy, sub_zero]) =
      S.abHomologyClass x hx - S.abHomologyClass y hy := by
  change S.homologyπ (S.abCyclesIso.inv ((⟨x, hx⟩ : S.g.hom.ker) - ⟨y, hy⟩)) = _
  simp only [map_sub, abHomologyClass]

variable {S T : ShortComplex AddCommGrpCat.{u}}

/-- A short-complex morphism sends cycle representatives through its middle component. -/
theorem homologyMap_abHomologyClass (φ : S ⟶ T)
    (x : S.X₂) (hx : S.g x = 0) (hy : T.g (φ.τ₂ x) = 0) :
    homologyMap φ (S.abHomologyClass x hx) = T.abHomologyClass (φ.τ₂ x) hy := by
  let c := S.abCyclesIso.inv (⟨x, hx⟩ : S.g.hom.ker)
  have hc : cyclesMap φ c = T.abCyclesIso.inv (⟨φ.τ₂ x, hy⟩ : T.g.hom.ker) := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).1 inferInstance
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply]
    exact (congrArg (fun a : S.X₂ => φ.τ₂ a)
      (S.abCyclesIso_inv_apply_iCycles ⟨x, hx⟩)).trans
        (T.abCyclesIso_inv_apply_iCycles ⟨φ.τ₂ x, hy⟩).symm
  exact (ConcreteCategory.congr_hom (homologyπ_naturality φ) c).trans
    (congrArg T.homologyπ hc)

/-- A map induces an isomorphism on homology when it reflects boundaries
of cycles and every target cycle agrees with an image up to a boundary. -/
theorem isIso_homologyMap_of_ab_representatives (φ : S ⟶ T)
    (hinj : ∀ (x : S.X₂), S.g x = 0 →
      (∃ b : T.X₁, T.f b = φ.τ₂ x) → ∃ a : S.X₁, S.f a = x)
    (hsurj : ∀ (y : T.X₂), T.g y = 0 →
      ∃ (x : S.X₂), S.g x = 0 ∧ ∃ b : T.X₁, T.f b = y - φ.τ₂ x) :
    IsIso (homologyMap φ) := by
  have hcycle (x : S.X₂) (hx : S.g x = 0) : T.g (φ.τ₂ x) = 0 := by
    rw [← ConcreteCategory.comp_apply, φ.comm₂₃, ConcreteCategory.comp_apply, hx, map_zero]
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · change Function.Injective (homologyMap φ).hom
    apply (injective_iff_map_eq_zero (homologyMap φ).hom).2
    intro c hc
    obtain ⟨x, hx, rfl⟩ := S.exists_abHomologyClass c
    rw [homologyMap_abHomologyClass φ x hx (hcycle x hx)] at hc
    exact (S.abHomologyClass_eq_zero_iff x hx).2
      (hinj x hx ((T.abHomologyClass_eq_zero_iff (φ.τ₂ x) (hcycle x hx)).1 hc))
  · intro c
    obtain ⟨y, hy, rfl⟩ := T.exists_abHomologyClass c
    obtain ⟨x, hx, b, hb⟩ := hsurj y hy
    refine ⟨S.abHomologyClass x hx, ?_⟩
    rw [homologyMap_abHomologyClass φ x hx (hcycle x hx)]
    have hsub : T.g (y - φ.τ₂ x) = 0 := by rw [map_sub, hy, hcycle x hx, sub_zero]
    have hzero := (T.abHomologyClass_eq_zero_iff (y - φ.τ₂ x) hsub).2 ⟨b, hb⟩
    rw [abHomologyClass_sub T y (φ.τ₂ x) hy (hcycle x hx)] at hzero
    exact (sub_eq_zero.mp hzero).symm

end CategoryTheory.ShortComplex
