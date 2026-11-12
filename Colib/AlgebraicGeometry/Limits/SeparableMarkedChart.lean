/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Limits.IntegralMarkedChart
public import Colib.AlgebraicGeometry.ResidueField.SeparableMarking

/-!
# Finite integral charts preserving an arbitrary separably closed marking

The actual residue-field factorization supplies a separable intermediate field.
The clopen integral-component model then lifts the original marking without
assuming that its field is algebraic over the base field.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory IntermediateField
universe u
namespace AlgebraicGeometry.Scheme

/-- The native subalgebra scalar structure fixes the intermediate-field scalar diamond. -/
local instance separableChartSubfieldAlgebra (E L : Type u) [Field E] [Field L] [Algebra E L]
    (t : Finset L) : Algebra E (adjoin E (t : Set L)) := (adjoin E (t : Set L)).toSubalgebra.algebra

/-- An arbitrary separably closed marking with separable residue lifts to an actual
finite separable integral chart, with the original coordinate count after base change. -/
theorem exists_separable_integral_marked_chart
    (E Ω B : Type u) [Field E] [Field Ω] [IsSepClosed Ω]
    [CommRing B] [Algebra E B] [Algebra.Smooth E B] {n : ℕ}
    (q : MvPolynomial (Fin n) E →ₐ[E] B) (hq : q.toRingHom.Etale)
    (ξ : Spec (.of Ω) ⟶ Spec (.of B))
    (hs : letI := (fieldToResidue (Spec.map (CommRingCat.ofHom (algebraMap E B)))
      (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable E ((Spec (.of B)).residueField (ξ (IsLocalRing.closedPoint Ω)))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra E L),
      IsSepClosed L ∧ Infinite L ∧ Algebra.IsSeparable E L ∧
      ∀ s : Finset L, ∃ t : Finset L, s ⊆ t ∧
        Module.Finite E (adjoin E (t : Set L)) ∧
        ∃ e : (adjoin E (t : Set L)) ⊗[E] B, IsIdempotentElem e ∧
          IsDomain (Localization.Away e) ∧
          IsDomain (L ⊗[adjoin E (t : Set L)] Localization.Away e) ∧
          Algebra.trdeg L (L ⊗[adjoin E (t : Set L)] Localization.Away e) = n ∧
          AlgebraicGeometry.Etale (finsetLocalizationToBase E L B t e) ∧
          ∃ ξ₁ : Spec (.of Ω) ⟶ Spec (.of (Localization.Away e)),
            ξ₁ ≫ finsetLocalizationToBase E L B t e = ξ := by
  obtain ⟨L, hField, hAlg, hClosed, hInf, hSep, φ, x, hx, hξ⟩ :=
    exists_separable_residue_marking
      (Spec.map (CommRingCat.ofHom (algebraMap E B))) ξ hs
  let := hField
  let := hAlg
  let := hSep
  refine ⟨L, hField, hAlg, hClosed, hInf, hSep, ?_⟩
  intro s
  obtain ⟨t, ht, hfin, e, he, hd, hdL, hdim, het, x₁, _, _, hmark, _⟩ :=
    exists_integral_marked_finsetSubfieldModel E L B q hq x hx
      (Spec.map (CommRingCat.ofHom φ)) s
  exact ⟨t, ht, hfin, e, he, hd, hdL, hdim, het,
    Spec.map (CommRingCat.ofHom φ) ≫ x₁, hmark.trans hξ⟩

end AlgebraicGeometry.Scheme
