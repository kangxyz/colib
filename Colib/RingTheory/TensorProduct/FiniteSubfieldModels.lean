/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.Localization.BaseChange
/-!
# Actual finite-subfield models of tensor elements and localizations

Every finite family in the original scalar extension `L ⊗[K] B` is already defined over one
actual finitely generated intermediate field `K(t)`, enlarging any prescribed finite scalar
set. The original tensor inclusions are injective. Equations, including idempotence, therefore
hold already at that stage. The localization maps are the native maps of the original tensor
inclusions, and the canonical iterated scalar-extension equivalence identifies their actual
base changes with the original principal opens. Two different localization elements remain
two different choices, even when modeled over the same stage.

For a separable algebraic extension, the stages are finite separable by
`IntermediateField.finite_finsetAdjoinDiagram_obj` in `FiniteSubfields`; no infinitude of the
base field or finite-type assumption on `B` is needed for the finite tensor-support argument.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace IntermediateField

variable (K L B : Type u) [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]

/-- The original scalar-extension inclusion from the actual finitely generated subfield. -/
def finsetTensorInclusion (s : Finset L) :
    (adjoin K (s : Set L)) ⊗[K] B →ₐ[K] L ⊗[K] B :=
  Algebra.TensorProduct.map (adjoin K (s : Set L)).val (AlgHom.id K B)

/-- The actual tensor map induced by inclusion of two scalar parameter sets. -/
def finsetTensorTransition {s t : Finset L} (h : s ⊆ t) :
    (adjoin K (s : Set L)) ⊗[K] B →ₐ[K] (adjoin K (t : Set L)) ⊗[K] B :=
  Algebra.TensorProduct.map (inclusion (adjoin.mono K _ _ (Finset.coe_subset.mpr h)))
    (AlgHom.id K B)

/-- Tensoring the actual subfield inclusions preserves their composition. -/
theorem tensorInclusion_transition (E F : IntermediateField K L) (h : E ≤ F) :
    (Algebra.TensorProduct.map F.val (AlgHom.id K B)).comp
        (Algebra.TensorProduct.map (inclusion h) (AlgHom.id K B)) =
      Algebra.TensorProduct.map E.val (AlgHom.id K B) := by
  rw [← Algebra.TensorProduct.map_comp]
  congr 1

/-- Original tensor inclusions commute with the actual finite-stage transition. -/
@[simp] theorem finsetTensorInclusion_transition {s t : Finset L} (h : s ⊆ t)
    (x : (adjoin K (s : Set L)) ⊗[K] B) :
    finsetTensorInclusion K L B t (finsetTensorTransition K L B h x) =
      finsetTensorInclusion K L B s x :=
  congrArg (fun φ : (adjoin K (s : Set L)) ⊗[K] B →ₐ[K] L ⊗[K] B => φ x)
    (tensorInclusion_transition K L B _ _
      (adjoin.mono K _ _ (Finset.coe_subset.mpr h)))

/-- An actual tensor inclusion is injective by flatness over the original field. -/
theorem finsetTensorInclusion_injective (s : Finset L) :
    Function.Injective (finsetTensorInclusion K L B s) := by
  exact TensorProduct.map_injective_of_flat_flat (adjoin K (s : Set L)).val.toLinearMap
    (AlgHom.id K B).toLinearMap (adjoin K (s : Set L)).val.injective Function.injective_id

/-- Each original tensor element has a model in one actual finite-generated subfield. -/
theorem exists_finsetTensor_preimage (x : L ⊗[K] B) :
    ∃ (s : Finset L) (y : (adjoin K (s : Set L)) ⊗[K] B),
      finsetTensorInclusion K L B s y = x := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact ⟨{a}, ⟨a, subset_adjoin K _ (Finset.mem_singleton_self a)⟩ ⊗ₜ[K] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨s, x', hx'⟩ := hx
    obtain ⟨t, y', hy'⟩ := hy
    refine ⟨s ∪ t, finsetTensorTransition K L B Finset.subset_union_left x' +
      finsetTensorTransition K L B Finset.subset_union_right y', ?_⟩
    simp only [map_add, finsetTensorInclusion_transition, hx', hy']

/-- The tensor model can enlarge a previously prescribed scalar parameter set. -/
theorem exists_finsetTensor_preimage_containing (s : Finset L) (x : L ⊗[K] B) :
    ∃ (t : Finset L), s ⊆ t ∧ ∃ y : (adjoin K (t : Set L)) ⊗[K] B,
      finsetTensorInclusion K L B t y = x := by
  classical
  obtain ⟨t, y, hy⟩ := exists_finsetTensor_preimage K L B x
  exact ⟨s ∪ t, Finset.subset_union_left,
    finsetTensorTransition K L B Finset.subset_union_right y, by simpa using hy⟩

/-- One actual stage models every member of a finite set of original tensor elements. -/
theorem exists_finsetTensor_preimages (s : Finset L) (q : Finset (L ⊗[K] B)) :
    ∃ (t : Finset L), s ⊆ t ∧ ∀ x ∈ q, ∃ y : (adjoin K (t : Set L)) ⊗[K] B,
      finsetTensorInclusion K L B t y = x := by
  classical
  induction q using Finset.induction_on with
  | empty => exact ⟨s, Finset.Subset.refl s, by simp⟩
  | @insert x q hx ih =>
    obtain ⟨t, ht, hq⟩ := ih
    obtain ⟨v, hv, y, hy⟩ := exists_finsetTensor_preimage_containing K L B t x
    refine ⟨v, ht.trans hv, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨y, hy⟩
    · obtain ⟨w, hw⟩ := hq z hz
      exact ⟨finsetTensorTransition K L B hv w, by simpa using hw⟩

/-- A whole finite indexed tuple descends to one actual stage, with exact image equations. -/
theorem exists_finsetTensor_family {ι : Type*} [Finite ι]
    (s : Finset L) (x : ι → L ⊗[K] B) :
    ∃ (t : Finset L), s ⊆ t ∧ ∃ y : ι → (adjoin K (t : Set L)) ⊗[K] B,
      ∀ i, finsetTensorInclusion K L B t (y i) = x i := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨t, ht, hy⟩ := exists_finsetTensor_preimages K L B s (Finset.univ.image x)
  have h (i : ι) := hy (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  choose y hy using h
  exact ⟨t, ht, y, hy⟩

/-- An original idempotent descends as an idempotent, with its original image unchanged. -/
theorem exists_finsetTensor_idempotent (s : Finset L) (e : L ⊗[K] B)
    (he : IsIdempotentElem e) :
    ∃ (t : Finset L), s ⊆ t ∧ ∃ e' : (adjoin K (t : Set L)) ⊗[K] B,
      finsetTensorInclusion K L B t e' = e ∧ IsIdempotentElem e' := by
  obtain ⟨t, ht, e', he'⟩ := exists_finsetTensor_preimage_containing K L B s e
  refine ⟨t, ht, e', he', ?_⟩
  apply finsetTensorInclusion_injective K L B t
  simpa only [map_mul, he'] using (show e * e = e from he)

/-- The native localization map of the actual finite-stage tensor inclusion. -/
def finsetTensorLocalizationMap (s : Finset L) (r : (adjoin K (s : Set L)) ⊗[K] B) :
    Localization.Away r →ₐ[K] Localization.Away (finsetTensorInclusion K L B s r) :=
  IsLocalization.Away.mapₐ _ _ (finsetTensorInclusion K L B s) r

/-- The original localization map remains injective. -/
theorem finsetTensorLocalizationMap_injective (s : Finset L)
    (r : (adjoin K (s : Set L)) ⊗[K] B) :
    Function.Injective (finsetTensorLocalizationMap K L B s r) :=
  IsLocalization.Away.mapₐ_injective_of_injective r (finsetTensorInclusion_injective K L B s)


end IntermediateField

namespace Algebra.TensorProduct

variable (K E L B : Type u) [Field K] [Field E] [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [CommRing B] [Algebra K B]

/-- The canonical iterated scalar-extension equivalence keeps the original inclusion map. -/
theorem cancelBaseChange_includeRight (x : E ⊗[K] B) :
    cancelBaseChange K E L L B ((1 : L) ⊗ₜ[E] x) =
      map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [cancelBaseChange_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The actual base change of a principal localization is the localization at the image of
its original element, via the canonical iterated scalar-extension equivalence. -/
def cancelBaseChangeAway (r : E ⊗[K] B) :
    L ⊗[E] Localization.Away r ≃ₐ[L]
      Localization.Away (map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r) :=
  (IsLocalization.Away.tensorProductEquivTMulRight E L r (Localization.Away r)).trans
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers ((1 : L) ⊗ₜ[E] r))
      (T := Submonoid.powers (map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))
      (Localization.Away ((1 : L) ⊗ₜ[E] r))
      (Localization.Away (map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))
      (cancelBaseChange K E L L B)
      (by simp only [Submonoid.map_powers, cancelBaseChange_includeRight]))

/-- The localization comparison retains the original scalar and numerator on pure tensors. -/
theorem cancelBaseChangeAway_tmul (r x : E ⊗[K] B) (a : L) :
    cancelBaseChangeAway K E L B r (a ⊗ₜ[E] algebraMap _ (Localization.Away r) x) =
      algebraMap _ (Localization.Away
        (map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))
        (cancelBaseChange K E L L B (a ⊗ₜ[E] x)) := by
  simp only [cancelBaseChangeAway, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq]

end Algebra.TensorProduct

namespace IntermediateField
variable (K L B : Type u) [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]

/-- Integrality of an original localized scalar extension descends to its actual stage. -/
theorem isDomain_finsetTensorLocalization (s : Finset L)
    (r : (adjoin K (s : Set L)) ⊗[K] B)
    [IsDomain (Localization.Away (finsetTensorInclusion K L B s r))] :
    IsDomain (Localization.Away r) :=
  Function.Injective.isDomain (finsetTensorLocalizationMap K L B s r)
    (finsetTensorLocalizationMap_injective K L B s r)

end IntermediateField
