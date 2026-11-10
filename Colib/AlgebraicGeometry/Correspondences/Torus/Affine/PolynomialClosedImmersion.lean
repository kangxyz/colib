/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialSpan
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The actual polynomial quotient is closed in the native torus ambient

The native ambient's coefficient homomorphism and its literal forward unit give
an actual polynomial-evaluation homomorphism. Its composite with the quotient
span is the original quotient map, not merely its radical. Surjectivity of that
composite proves that the span is a closed immersion. No Laurent replacement
scheme or assumption about a coordinate chart is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R]

/-- The original source-first ambient, with no change of torus model. -/
abbrev ambient (f : Spec (.of R) ⟶ S) :=
  pullback f (multiplicativeGroupBaseChange S ↘ S)

/-- The coefficient map from the actual first projection. -/
def ambientCoefficient (f : Spec (.of R) ⟶ S) : R →+* Γ(ambient f, ⊤) :=
  (pullback.fst f (multiplicativeGroupBaseChange S ↘ S)).appTop.hom.comp
    (Scheme.ΓSpecIso (.of R)).inv.hom

/-- The literal forward unit pulled back along the actual second projection. -/
def ambientCoordinate (f : Spec (.of R) ⟶ S) : (Γ(ambient f, ⊤))ˣ :=
  Units.map (pullback.snd f (multiplicativeGroupBaseChange S ↘ S)).appTop.hom.toMonoidHom
    (multiplicativeGroupBaseChangeCoordinate S)

/-- Evaluate coefficient polynomials in the actual native ambient global sections. -/
def ambientPolynomial (f : Spec (.of R) ⟶ S) : R[X] →+* Γ(ambient f, ⊤) :=
  eval₂RingHom (ambientCoefficient f) (ambientCoordinate f).val

@[simp] theorem ambientPolynomial_C (f : Spec (.of R) ⟶ S) (r : R) :
    ambientPolynomial f (C r) = ambientCoefficient f r := by
  simp [ambientPolynomial]

@[simp] theorem ambientPolynomial_X (f : Spec (.of R) ⟶ S) :
    ambientPolynomial f Polynomial.X = (ambientCoordinate f).val := by
  simp [ambientPolynomial]

/-- The actual quotient span pulls a coefficient back by the original quotient map. -/
theorem inclusion_appTop_coefficient (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hu : IsUnit (p.coeff 0)) (r : R) :
    (inclusion f p hu).appTop (ambientCoefficient f r) =
      (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv (AdjoinRoot.of p r) := by
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (AdjoinRoot.of p))) r
  have hi := congrArg (fun k => k.appTop) (inclusion_fst f p hu)
  rw [Scheme.Hom.comp_appTop] at hi
  change ((pullback.fst f (multiplicativeGroupBaseChange S ↘ S)).appTop ≫ (inclusion f p hu).appTop)
      ((Scheme.ΓSpecIso (.of R)).inv r) = _
  rw [hi]
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The span pulls the ambient forward coordinate back to the literal root. -/
theorem inclusion_appTop_coordinate (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (inclusion f p hu).appTop (ambientCoordinate f).val =
      (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv (AdjoinRoot.root p) := by
  have hi := congrArg (fun k => k.appTop) (inclusion_snd f p hu)
  rw [Scheme.Hom.comp_appTop] at hi
  change ((pullback.snd f (multiplicativeGroupBaseChange S ↘ S)).appTop ≫ (inclusion f p hu).appTop)
      (multiplicativeGroupBaseChangeCoordinate S).val = _
  rw [hi]
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (AdjoinRoot p))).hom).1
  rw [CommRingCat.hom_inv_apply]
  change (coordinateUnit f p hu : AdjoinRoot p) = AdjoinRoot.root p
  exact coordinateUnit_val f p hu

/-- The original whole quotient homomorphism, including nilpotents, is recovered exactly. -/
theorem inclusion_appTop_ambientPolynomial (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (inclusion f p hu).appTop.hom.comp (ambientPolynomial f) =
      (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv.hom.comp (AdjoinRoot.mk p) := by
  apply Polynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, ambientPolynomial_C, AdjoinRoot.mk_C] using
      inclusion_appTop_coefficient f p hu r
  · simpa only [RingHom.comp_apply, ambientPolynomial_X, AdjoinRoot.mk_X] using
      inclusion_appTop_coordinate f p hu

/-- Every actual global section on the quotient comes from the native torus ambient. -/
theorem inclusion_appTop_surjective (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    Function.Surjective (inclusion f p hu).appTop := by
  have h : Function.Surjective
      ((inclusion f p hu).appTop.hom.comp (ambientPolynomial f)) := by
    rw [inclusion_appTop_ambientPolynomial]
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv).2.comp (AdjoinRoot.mk_surjective (g := p))
  intro b
  obtain ⟨a, ha⟩ := h b
  exact ⟨ambientPolynomial f a, ha⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine source makes the existing native torus ambient affine. -/
theorem ambient_isAffine (f : Spec (.of R) ⟶ S) : IsAffine (ambient f) := by
  have : IsAffineHom (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom LaurentPolynomial.C))
    infer_instance
  have : IsAffineHom (multiplicativeGroupBaseChange S ↘ S) := by
    change IsAffineHom (pullback.snd
      (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S))
    exact MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  change IsAffine (pullback f (multiplicativeGroupBaseChange S ↘ S))
  infer_instance

/-- The actual polynomial span is a closed immersion into the native torus ambient. -/
theorem inclusion_isClosedImmersion (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hu : IsUnit (p.coeff 0)) : IsClosedImmersion (inclusion f p hu) := by
  have := ambient_isAffine f
  exact IsClosedImmersion.of_surjective_of_isAffine _ (inclusion_appTop_surjective f p hu)

end AlgebraicGeometry.NativeTorusPolynomial
