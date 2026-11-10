/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.RationalDivisor

/-!
# Native ambient independence for the fixed affine coefficient ring

Changing the original base scheme and source structure map does not change
the native polynomial divisor after the explicit coordinate-preserving
ambient isomorphism. This is a genuine scheme-isomorphism naturality result.
It is not coefficient specialization to a different ring or global descent.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial Stacks.Chow
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S T : Scheme.{u}} {R : Type u} [CommRing R]

/-- The explicit coordinate-preserving isomorphism of the two actual native ambients. -/
def ambientChangeIso (f : Spec (.of R) ⟶ S) (g : Spec (.of R) ⟶ T) : ambient f ≅ ambient g :=
  (nativeChartIso f).symm ≪≫ nativeChartIso g

@[reassoc] theorem inclusion_ambientChangeIso
    (f : Spec (.of R) ⟶ S) (g : Spec (.of R) ⟶ T)
    (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    inclusion f p hu ≫ (ambientChangeIso f g).hom = inclusion g p hu := by
  rw [← chartQuotient_chartMap f]
  simp only [ambientChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact chartQuotient_chartMap g p hu

variable [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual native whole cycles commute with the coordinate-preserving ambient isomorphism. -/
theorem polynomialCycle_ambientChangeIso
    (f : Spec (.of R) ⟶ S) (g : Spec (.of R) ⟶ T)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    finiteCyclePushforward (ambientChangeIso f g).hom (polynomialCycle f p hp hu).val =
      (polynomialCycle g p hp hu).val := by
  have := quotient_isNoetherian p
  have := inclusion_isClosedImmersion f p hu
  have := inclusion_isClosedImmersion g p hu
  rw [polynomialCycle_val, polynomialCycle_val]
  have h := finiteCyclePushforward_comp_apply (inclusion f p hu) (ambientChangeIso f g).hom
    (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p))))
  simpa only [inclusion_ambientChangeIso] using h

/-- The genuine signed rational divisor has the same native ambient independence. -/
theorem rationalDivisor_ambientChangeIso
    (f : Spec (.of R) ⟶ S) (g : Spec (.of R) ⟶ T) (a : admissibleGroup R) :
    finiteCyclePushforward (ambientChangeIso f g).hom (rationalDivisor f a).val =
      (rationalDivisor g a).val := by
  obtain ⟨p, q, ha⟩ := a.property
  rw [rationalDivisor_eq f a p q ha, rationalDivisor_eq g a p q ha]
  change finiteCyclePushforward (ambientChangeIso f g).hom
      ((polynomialCycle f p.val p.property.1 p.property.2).val -
        (polynomialCycle f q.val q.property.1 q.property.2).val) = _
  rw [map_sub, polynomialCycle_ambientChangeIso, polynomialCycle_ambientChangeIso]
  rfl

end AlgebraicGeometry.NativeTorusPolynomial
