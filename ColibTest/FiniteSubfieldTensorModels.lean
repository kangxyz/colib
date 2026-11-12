/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.TensorProduct.FiniteSubfieldModels
import Colib.FieldTheory.Separable.FiniteSubfields

open scoped TensorProduct
open IntermediateField

universe u

/-- The etale-near-point element and the distinct whole-fiber element are modeled together,
without identifying their principal opens. The field need not be infinite. -/
example (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] (s : Finset L) (rₑ r : L ⊗[K] B) :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      ∃ rₑ' r' : (adjoin K (t : Set L)) ⊗[K] B,
        finsetTensorInclusion K L B t rₑ' = rₑ ∧ finsetTensorInclusion K L B t r' = r := by
  let v : Bool → L ⊗[K] B := fun i => if i then rₑ else r
  obtain ⟨t, ht, w, hw⟩ := exists_finsetTensor_family K L B s v
  exact ⟨t, ht, finite_finsetAdjoinDiagram_obj K L t, w true, w false, hw true, hw false⟩

/-- The original idempotent component has an integral actual finite-stage localization. -/
example (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] (s : Finset L) (e : L ⊗[K] B) (he : IsIdempotentElem e)
    [IsDomain (Localization.Away e)] :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      ∃ e' : (adjoin K (t : Set L)) ⊗[K] B,
        finsetTensorInclusion K L B t e' = e ∧ IsIdempotentElem e' ∧
          IsDomain (Localization.Away e') := by
  obtain ⟨t, ht, e', hmap, hidem⟩ := exists_finsetTensor_idempotent K L B s e he
  have : IsDomain (Localization.Away (finsetTensorInclusion K L B t e')) :=
    hmap.symm ▸ inferInstance
  exact ⟨t, ht, finite_finsetAdjoinDiagram_obj K L t, e', hmap, hidem,
    isDomain_finsetTensorLocalization K L B t e'⟩

/-- The native localization comparison is the original numerator map after scalar extension. -/
example (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [CommRing B] [Algebra K B] (r x : E ⊗[K] B) :
    Algebra.TensorProduct.cancelBaseChangeAway K E L B r
        ((1 : L) ⊗ₜ[E] algebraMap _ (Localization.Away r) x) =
      algebraMap _ (Localization.Away
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) r))
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B) x) := by
  rw [Algebra.TensorProduct.cancelBaseChangeAway_tmul,
    Algebra.TensorProduct.cancelBaseChange_includeRight]
