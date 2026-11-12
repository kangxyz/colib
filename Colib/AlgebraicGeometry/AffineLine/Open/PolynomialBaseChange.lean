/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Ambient
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Polynomial coordinates after an affine base restriction

The inverse image of an affine open in the polynomial line is the
polynomial line over its actual section ring. The comparison retains
both projections of the original Cartesian square.

Adapted from the target base-change and marked-base-change comparisons
in Motivic's `Aglib/AlgebraicGeometry/ProjectiveLine/Neighborhood/Target`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme

variable (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

/-- The coefficient homomorphism is induced by the actual affine open immersion. -/
abbrev affineOpenCoefficientMap : R →+* Γ(O.toScheme, ⊤) :=
  (Spec.preimage (O.toScheme.isoSpec.inv ≫ O.ι)).hom

private theorem affineOpenPolynomial_isPullback :
    IsPullback (polynomialProjection (.of Γ(O.toScheme, ⊤)) ≫ O.toScheme.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (affineOpenCoefficientMap R O))))
      O.ι (polynomialProjection (.of R)) := by
  have h := PolynomialOpenQuotient.ambient_isPullback (affineOpenCoefficientMap R O)
  refine h.of_iso (Iso.refl _) O.toScheme.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) ?_ (by simp)
  change Spec.map (Spec.preimage (O.toScheme.isoSpec.inv ≫ O.ι)) ≫ 𝟙 _ =
    O.toScheme.isoSpec.inv ≫ O.ι
  rw [Category.comp_id, Spec.map_preimage]

/-- The literal inverse image of the affine base open in the polynomial line. -/
@[no_expose]
def polynomialLineAffineOpenIso :
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) ≅
      (polynomialProjection (.of R) ⁻¹ᵁ O).toScheme :=
  (affineOpenPolynomial_isPullback R O).isoPullback ≪≫
    (isPullback_morphismRestrict (polynomialProjection (.of R)) O).isoPullback.symm

/-- The inverse comparison followed by polynomial coefficient restriction is the original
open inclusion. -/
@[reassoc]
theorem polynomialLineAffineOpenIso_inv_coordinate :
    (polynomialLineAffineOpenIso R O).inv ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (affineOpenCoefficientMap R O))) =
        (polynomialProjection (.of R) ⁻¹ᵁ O).ι := by
  let h := affineOpenPolynomial_isPullback R O
  let k := isPullback_morphismRestrict (polynomialProjection (.of R)) O
  calc
    _ = (k.isoPullback.hom ≫ h.isoPullback.inv) ≫
        (h.isoPullback.hom ≫ pullback.snd _ _) :=
      congrArg (fun a ↦ (k.isoPullback.hom ≫ h.isoPullback.inv) ≫ a)
        h.isoPullback_hom_snd.symm
    _ = _ := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact k.isoPullback_hom_snd

/-- The inverse comparison preserves the original base projection. -/
@[reassoc]
theorem polynomialLineAffineOpenIso_inv_projection :
    (polynomialLineAffineOpenIso R O).inv ≫ polynomialProjection (.of Γ(O.toScheme, ⊤)) =
      (polynomialProjection (.of R) ∣_ O) ≫ O.toScheme.isoSpec.hom := by
  apply (cancel_mono O.toScheme.isoSpec.inv).mp
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let h := affineOpenPolynomial_isPullback R O
  let k := isPullback_morphismRestrict (polynomialProjection (.of R)) O
  calc
    _ = (k.isoPullback.hom ≫ h.isoPullback.inv) ≫
        (h.isoPullback.hom ≫ pullback.fst _ _) :=
      congrArg (fun a ↦ (k.isoPullback.hom ≫ h.isoPullback.inv) ≫ a)
        h.isoPullback_hom_fst.symm
    _ = _ := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact k.isoPullback_hom_fst

end AlgebraicGeometry.Scheme
