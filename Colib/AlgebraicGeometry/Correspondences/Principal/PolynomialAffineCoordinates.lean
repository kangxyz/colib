/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Polynomial.LaurentBaseChange
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen

/-!
# Canonical polynomial coordinates of the original affine cylinder

The coefficient homomorphism comes from the original structure morphism and
its global-Spec comparison. The canonical polynomial pushout identifies the
original cylinder, retaining both its projection and literal parameter map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The original scalar map on global sections. -/
def affineScalar : k →+* Γ(X, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The canonical affine presentation retains the original structure map. -/
theorem affineScalar_spec [IsAffine X] :
    Spec.map (CommRingCat.ofHom (affineScalar p)) = X.isoSpec.inv ≫ p := by
  rw [← Scheme.isoSpec_inv_naturality p, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The literal polynomial spectrum has the original scalar-extension square. -/
theorem polynomialScalar_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, ⊤) →+* Γ(X, ⊤)[X])))
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (affineScalar p))))
      (Spec.map (CommRingCat.ofHom (affineScalar p)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout
      (CommRingCat.ofHom (affineScalar p)))

variable [IsAffine X]

/-- The canonical comparison into the actual original polynomial cylinder. -/
def affinePolynomialIso : Spec (.of Γ(X, ⊤)[X]) ≅ parameterSpace p :=
  (polynomialScalar_isPullback p).isoPullback ≪≫
    asIso (pullback.map (Spec.map (CommRingCat.ofHom (affineScalar p)))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) p
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
      X.isoSpec.inv (𝟙 _) (𝟙 _) (by simp [affineScalar_spec]) (by simp))

/-- The actual source projection is preserved, including its canonical affine chart. -/
theorem affinePolynomialIso_projection :
    (affinePolynomialIso p).hom ≫ projection p =
      Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, ⊤) →+* Γ(X, ⊤)[X])) ≫
        X.isoSpec.inv := by
  simp only [affinePolynomialIso, Iso.trans_hom, asIso_hom, projection, Category.assoc,
    pullback.map, pullback.lift_fst]
  rw [← Category.assoc, IsPullback.isoPullback_hom_fst]

/-- The actual polynomial parameter is the coefficient-extension map. -/
theorem affinePolynomialIso_parameter :
    (affinePolynomialIso p).hom ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) =
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (affineScalar p))) := by
  simp only [affinePolynomialIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_snd, Category.comp_id, IsPullback.isoPullback_hom_snd]

/-- Literal evaluation in canonical affine coordinates is the original endpoint section. -/
theorem affinePolynomialIso_endpoint (c : k) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (affineScalar p c))) ≫
      (affinePolynomialIso p).hom = X.isoSpec.inv ≫ endpoint p c := by
  apply pullback.hom_ext
  · rw [Category.assoc, affinePolynomialIso_projection]
    simp only [endpoint, Category.assoc, pullback.lift_fst, Category.comp_id]
    rw [← Category.assoc, ← Spec.map_comp]
    have H : CommRingCat.ofHom (Polynomial.C : Γ(X, ⊤) →+* Γ(X, ⊤)[X]) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (affineScalar p c)) = 𝟙 _ := by
      ext x
      exact Polynomial.eval_C
    rw [H, Spec.map_id, Category.id_comp]
  · rw [Category.assoc, affinePolynomialIso_parameter]
    simp only [endpoint, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, ← affineScalar_spec, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro x
      simp
    · simp

/-- The original endpoint square is cartesian over literal coefficient evaluation. -/
theorem affinePolynomialIso_endpoint_isPullback (c : k) :
    IsPullback (endpoint p c) X.isoSpec.hom (affinePolynomialIso p).inv
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (affineScalar p c)))) := by
  apply IsPullback.of_vert_isIso
  constructor
  apply (cancel_mono (affinePolynomialIso p).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [affinePolynomialIso_endpoint, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]

end AlgebraicGeometry.PrincipalFamilyUnitOpen
