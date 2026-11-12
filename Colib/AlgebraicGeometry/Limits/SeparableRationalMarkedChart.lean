/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Limits.SeparableMarkedChart

/-!
# Finite integral charts preserving an arbitrary separably closed marking

Retain the intermediate field map and its rational point, rather than only their
composite with the original geometric marking. This supplies the rational input
to finite-stage quadratic descent without selecting another component or point.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory IntermediateField
universe u
namespace AlgebraicGeometry.Scheme

/-- Use the native subalgebra scalar structure for the intermediate field. -/
local instance rationalChartSubfieldAlgebra (E L : Type u) [Field E] [Field L] [Algebra E L]
    (t : Finset L) : Algebra E (adjoin E (t : Set L)) := (adjoin E (t : Set L)).toSubalgebra.algebra

/-- An arbitrary separably closed marking with separable residue lifts to an actual
finite separable integral chart, retaining the same rational point and its field map. -/
theorem exists_separable_integral_rational_marked_chart
    (E Ω B : Type u) [Field E] [Field Ω] [IsSepClosed Ω]
    [CommRing B] [Algebra E B] [Algebra.Smooth E B] {n : ℕ}
    (q : MvPolynomial (Fin n) E →ₐ[E] B) (hq : q.toRingHom.Etale)
    (ξ : Spec (.of Ω) ⟶ Spec (.of B))
    (hs : letI := (fieldToResidue (Spec.map (CommRingCat.ofHom (algebraMap E B)))
      (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable E ((Spec (.of B)).residueField (ξ (IsLocalRing.closedPoint Ω)))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra E L),
      IsSepClosed L ∧ Infinite L ∧ Algebra.IsSeparable E L ∧
      ∃ (φ : L →+* Ω) (x : Spec (.of L) ⟶ Spec (.of B)),
        x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) =
          Spec.map (CommRingCat.ofHom (algebraMap E L)) ∧
        Spec.map (CommRingCat.ofHom φ) ≫ x = ξ ∧
      ∀ s : Finset L, ∃ t : Finset L, s ⊆ t ∧
        Module.Finite E (adjoin E (t : Set L)) ∧
        ∃ e : (adjoin E (t : Set L)) ⊗[E] B, IsIdempotentElem e ∧
          IsDomain (Localization.Away e) ∧
          IsDomain (L ⊗[adjoin E (t : Set L)] Localization.Away e) ∧
          Algebra.trdeg L (L ⊗[adjoin E (t : Set L)] Localization.Away e) = n ∧
          AlgebraicGeometry.Etale (finsetLocalizationToBase E L B t e) ∧
          ∃ x₁ : Spec (.of L) ⟶ Spec (.of (Localization.Away e)),
            x₁ ≫ finsetLocalizationToBase E L B t e = x ∧
            x₁ ≫ finsetLocalizationToField E L B t e =
              Spec.map (CommRingCat.ofHom (adjoin E (t : Set L)).val.toRingHom) ∧
            (Spec.map (CommRingCat.ofHom φ) ≫ x₁) ≫
              finsetLocalizationToBase E L B t e = ξ := by
  obtain ⟨L, hField, hAlg, hClosed, hInf, hSep, φ, x, hx, hξ⟩ :=
    exists_separable_residue_marking
      (Spec.map (CommRingCat.ofHom (algebraMap E B))) ξ hs
  let := hField
  let := hAlg
  let := hSep
  refine ⟨L, hField, hAlg, hClosed, hInf, hSep, φ, x, hx, hξ, ?_⟩
  intro s
  obtain ⟨t, ht, hfin, e, he, hd, hdL, hdim, het, x₁, hx₁, hxField, hmark, _⟩ :=
    exists_integral_marked_finsetSubfieldModel E L B q hq x hx
      (Spec.map (CommRingCat.ofHom φ)) s
  exact ⟨t, ht, hfin, e, he, hd, hdL, hdim, het,
    x₁, hx₁, hxField, hmark.trans hξ⟩


end AlgebraicGeometry.Scheme
