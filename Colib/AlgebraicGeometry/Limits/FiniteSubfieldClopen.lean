/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.TensorProduct.FiniteSubfieldModels
public import Colib.FieldTheory.Separable.FiniteSubfields
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
/-!
# An actual finite-subfield model of an integral affine clopen open

Native idempotents identify the original clopen open with a principal open. The actual tensor
inclusion descends that idempotent, and the native basic-open spectrum isomorphism retains the
original inclusion into the affine scalar extension. Domain descent supplies integrality of
the finite-stage localization. The scalar extension/localization comparison itself is the
canonical `Algebra.TensorProduct.cancelBaseChangeAway`.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory IntermediateField

universe u

namespace AlgebraicGeometry.Scheme

/-- An original integral affine clopen open comes from an actual finite-stage idempotent,
with the exact original inclusion equation and an integral stage localization. -/
theorem exists_integral_clopen_finsetSubfieldModel
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] (s : Finset L)
    (U : (Spec (.of (L ⊗[K] B))).Opens) (hU : IsClopen (U : Set (Spec (.of (L ⊗[K] B)))))
    [IsIntegral U.toScheme] :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      ∃ e : (adjoin K (t : Set L)) ⊗[K] B, IsIdempotentElem e ∧
        IsDomain (Localization.Away e) ∧
        ∃ i : U.toScheme ≅ Spec (.of (Localization.Away (finsetTensorInclusion K L B t e))),
          i.hom ≫ Spec.map (CommRingCat.ofHom
            (algebraMap (L ⊗[K] B) (Localization.Away (finsetTensorInclusion K L B t e)))) =
              U.ι := by
  obtain ⟨e, he, h⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hU
  have hU' : U = PrimeSpectrum.basicOpen e := SetLike.ext' h
  subst U
  have hInt : IsIntegral (Spec (.of (Localization.Away e))) :=
    IsIntegral.of_isIso (basicOpenIsoSpecAway (R := .of (L ⊗[K] B)) e).hom
  have : IsDomain (Localization.Away e) := (affine_isIntegral_iff _).mp hInt
  obtain ⟨t, ht, e', hmap, hidem⟩ := exists_finsetTensor_idempotent K L B s e he
  subst e
  exact ⟨t, ht, finite_finsetAdjoinDiagram_obj K L t, e', hidem,
    isDomain_finsetTensorLocalization K L B t e',
    basicOpenIsoSpecAway _, basicOpenIsoSpecAway_hom_SpecMap _⟩

end AlgebraicGeometry.Scheme
