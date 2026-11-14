/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import StacksFrontier.Homology.Perfect.Basic

/-! # Finite projective models of two-term complexes

A two-term complex of projective modules that represents a perfect object is
homotopy equivalent to a two-term complex of finite projective modules.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- A derived isomorphism between K-projective complexes lifts to a chain homotopy equivalence. -/
noncomputable def homotopyEquivOfDerivedIso {K L : CochainComplex C ℤ}
    [K.IsKProjective] [L.IsKProjective]
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) : HomotopyEquiv K L := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let F := DerivedCategory.Qh (C := C)
  let c := DerivedCategory.quotientCompQhIso C
  let e' : F.obj (q.obj K) ≅ F.obj (q.obj L) := c.app K ≪≫ e ≪≫ (c.app L).symm
  let f := ((IsKProjective.Qh_map_bijective K (q.obj L)).surjective e'.hom).choose
  let g := ((IsKProjective.Qh_map_bijective L (q.obj K)).surjective e'.inv).choose
  have hf := ((IsKProjective.Qh_map_bijective K (q.obj L)).surjective e'.hom).choose_spec
  have hg := ((IsKProjective.Qh_map_bijective L (q.obj K)).surjective e'.inv).choose_spec
  exact HomotopyCategory.homotopyEquivOfIso {
    hom := f
    inv := g
    hom_inv_id := (IsKProjective.Qh_map_bijective K (q.obj K)).injective (by
      rw [F.map_comp, F.map_id, hf, hg, e'.hom_inv_id])
    inv_hom_id := (IsKProjective.Qh_map_bijective L (q.obj L)).injective (by
      rw [F.map_comp, F.map_id, hf, hg, e'.inv_hom_id]) }

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

/-- A two-term complex of projectives representing a perfect object has a chain homotopy
equivalence to a complex of finite projectives in the same two degrees. -/
theorem exists_finiteProjectiveTwoTermModel (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    [K.IsStrictlyGE 0] [K.IsStrictlyLE 1] [∀ i : ℤ, Module.Projective R (K.X i)]
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj K)) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      Nonempty (HomotopyEquiv K P) := by
  have h := StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension
    (DerivedCategory.Q.obj K)
  have hflat : StacksDraft.Perfect.HasFlatRepresentative (DerivedCategory.Q.obj K) 0 1 :=
    ⟨K, fun i ↦ inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  obtain ⟨P, hP, hge, hle, ⟨e⟩⟩ := h.2 0 1 (h.1.mp hK).1 hflat
  let : P.IsStrictlyGE 0 := hge
  let : P.IsStrictlyLE 1 := hle
  let (i : ℤ) : Module.Projective R (P.X i) := (hP i).2
  let (i : ℤ) : Projective (P.X i) := inferInstance
  let (i : ℤ) : Projective (K.X i) := inferInstance
  let : K.IsKProjective := isKProjective_of_projective K 1
  let : P.IsKProjective := isKProjective_of_projective P 1
  refine ⟨P, ?_, hP, ⟨homotopyEquivOfDerivedIso e⟩⟩
  intro k hzero hone
  by_cases hneg : k < 0
  · exact P.isZero_of_isStrictlyGE 0 k hneg
  · exact P.isZero_of_isStrictlyLE 1 k (by omega)

end CochainComplex
