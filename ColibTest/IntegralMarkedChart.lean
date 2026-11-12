/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Limits.IntegralMarkedChart
import Colib.AlgebraicGeometry.Limits.SeparableMarkedChart

/-! # Tests of finite integral charts with their original geometric marking -/

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme IntermediateField

universe u

noncomputable section

local instance (E L : Type u) [Field E] [Field L] [Algebra E L] (t : Finset L) :
    Algebra E (adjoin E (t : Set L)) := (adjoin E (t : Set L)).toSubalgebra.algebra

set_option backward.isDefEq.respectTransparency false in
example (E L B Ω : Type u) [Field E] [Field L] [Field Ω]
    [Algebra E L] [Algebra.IsSeparable E L] [CommRing B] [Algebra E B]
    [Algebra.Smooth E B] {n : ℕ}
    (q : MvPolynomial (Fin n) E →ₐ[E] B) (hq : q.toRingHom.Etale)
    (x : Spec (.of L) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) =
      Spec.map (CommRingCat.ofHom (algebraMap E L)))
    (φ : L →+* Ω) (ξ : Spec (.of Ω) ⟶ Spec (.of B))
    (hξ : Spec.map (CommRingCat.ofHom φ) ≫ x = ξ) :
    ∃ (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B),
      Module.Finite E (adjoin E (t : Set L)) ∧ IsIdempotentElem e ∧
      IsDomain (Localization.Away e) ∧
      IsDomain (L ⊗[adjoin E (t : Set L)] Localization.Away e) ∧
      Algebra.trdeg L (L ⊗[adjoin E (t : Set L)] Localization.Away e) = n ∧
      AlgebraicGeometry.Etale (finsetLocalizationToBase E L B t e) ∧
      ∃ ξ₁ : Spec (.of Ω) ⟶ Spec (.of (Localization.Away e)),
        ξ₁ ≫ finsetLocalizationToBase E L B t e = ξ := by
  obtain ⟨t, _, hfin, e, he, hd, hdL, hdim, het, x₁, _, _, hmark, _⟩ :=
    exists_integral_marked_finsetSubfieldModel E L B q hq x hx
      (Spec.map (CommRingCat.ofHom φ)) ∅
  exact ⟨t, e, hfin, he, hd, hdL, hdim, het,
    Spec.map (CommRingCat.ofHom φ) ≫ x₁, hmark.trans hξ⟩

example (E L B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing B] [Algebra E B] {n : ℕ}
    (q : MvPolynomial (Fin n) E →ₐ[E] B) (hq : q.toRingHom.Etale)
    (e : L ⊗[E] B) [IsDomain (Localization.Away e)] :
    Algebra.trdeg L (Localization.Away e) = n :=
  Algebra.trdeg_localized_tensor_of_etale_polynomial_map E L B q hq e

/-- No algebraicity assumption on Omega enters the original-marking consumer. -/
example (E Ω B : Type u) [Field E] [Field Ω] [IsSepClosed Ω]
    [CommRing B] [Algebra E B] [Algebra.Smooth E B] {n : ℕ}
    (q : MvPolynomial (Fin n) E →ₐ[E] B) (hq : q.toRingHom.Etale)
    (ξ : Spec (.of Ω) ⟶ Spec (.of B))
    (hs : letI := (fieldToResidue (Spec.map (CommRingCat.ofHom (algebraMap E B)))
      (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable E ((Spec (.of B)).residueField (ξ (IsLocalRing.closedPoint Ω)))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra E L), Infinite L ∧
      ∃ (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B),
        IsDomain (Localization.Away e) ∧
        AlgebraicGeometry.Etale (finsetLocalizationToBase E L B t e) ∧
        ∃ ξ₁ : Spec (.of Ω) ⟶ Spec (.of (Localization.Away e)),
          ξ₁ ≫ finsetLocalizationToBase E L B t e = ξ := by
  obtain ⟨L, hField, hAlg, _, hInf, _, h⟩ :=
    exists_separable_integral_marked_chart E Ω B q hq ξ hs
  let := hField
  let := hAlg
  obtain ⟨t, _, _, e, _, hd, _, _, het, ξ₁, hξ₁⟩ := h ∅
  exact ⟨L, hField, hAlg, hInf, t, e, hd, het, ξ₁, hξ₁⟩
