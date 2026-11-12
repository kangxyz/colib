/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.LaurentComplementBaseChange
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineComparison

/-!
# The existing native polynomial zero is the base-changed integral zero

The comparison uses the actual affine-space coordinate and the existing
nativePolynomialAffineLineIso, so it determines the specified zero map,
not merely some section of the affine-line projection.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry

/-- The univariate comparison retains its actual forward coordinate. -/
theorem polynomialAffineSpaceIso_hom_appTop_coord (R : CommRingCat.{u})
    (i : ULift.{u} Unit) :
    (polynomialAffineSpaceIso R).hom.appTop (AffineSpace.coord (Spec R) i) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X := by
  simp only [polynomialAffineSpaceIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.op_hom, Scheme.Spec_map, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  let f := Spec.map (CommRingCat.ofHom
    (MvPolynomial.uniqueAlgEquiv R (ULift.{u} Unit)).toRingHom)
  change f.appTop ((AffineSpace.SpecIso (ULift.{u} Unit) R).inv.appTop
    (AffineSpace.coord (Spec R) i)) = _
  calc
    _ = f.appTop ((Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} Unit) R))).inv
        (MvPolynomial.X i)) :=
      congrArg (fun x => f.appTop x)
        (AffineSpace.SpecIso_inv_appTop_coord (n := ULift.{u} Unit) R i)
    _ = _ := by
      dsimp only [f]
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        CommRingCat.comp_apply]
      change (Scheme.ΓSpecIso (.of (Polynomial R))).inv
        ((MvPolynomial.uniqueAlgEquiv R (ULift.{u} Unit)) (MvPolynomial.X i)) = _
      simp [MvPolynomial.uniqueAlgEquiv_apply]

/-- Literal evaluation at zero has zero affine-space coordinate. -/
theorem polynomial_zero_affineSpace_coord (R : CommRingCat.{u}) (i : ULift.{u} Unit) :
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
      (polynomialAffineSpaceIso R).hom).appTop (AffineSpace.coord (Spec R) i) = 0 := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    polynomialAffineSpaceIso_hom_appTop_coord]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]
  simp

/-- The actual affine-space comparison preserves the integral projection. -/
@[reassoc]
theorem additiveGroupBaseChangeAffineSpaceIso_hom_map (S : Scheme.{u}) :
    (additiveGroupBaseChangeAffineSpaceIso S).hom ≫
      AffineSpace.map (ULift.{u} Unit) (specULiftZIsTerminal.from S) =
      pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S) ≫ additiveGroupAffineSpaceIso.hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- Zero is retained by the actual affine-space base-change map. -/
theorem polynomial_zero_affineSpace_map (R : CommRingCat.{u}) :
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
      (polynomialAffineSpaceIso R).hom) ≫
        AffineSpace.map (ULift.{u} Unit) (specULiftZIsTerminal.from (Spec R)) =
      specULiftZIsTerminal.from (Spec R) ≫ integralAdditiveZero ≫
        additiveGroupAffineSpaceIso.hom := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.map_over,
      polynomialAffineSpaceIso_hom_over_assoc,
      additiveGroupAffineSpaceIso_hom_over, integralAdditiveZero_over,
      Category.comp_id]
    exact specULiftZIsTerminal.hom_ext _ _
  · intro i
    change (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
      (polynomialAffineSpaceIso R).hom).appTop
        ((AffineSpace.map (ULift.{u} Unit) (specULiftZIsTerminal.from (Spec R))).appTop
          (AffineSpace.coord _ i)) = _
    rw [AffineSpace.map_appTop_coord, polynomial_zero_affineSpace_coord]
    change 0 = (specULiftZIsTerminal.from (Spec R)).appTop
      ((integralAdditiveZero ≫ additiveGroupAffineSpaceIso.hom).appTop
        (AffineSpace.coord _ i))
    have hz := polynomial_zero_affineSpace_coord (.of (ULift.{u} ℤ)) i
    change (integralAdditiveZero ≫ additiveGroupAffineSpaceIso.hom).appTop
      (AffineSpace.coord _ i) = 0 at hz
    rw [hz, map_zero]

/-- The base-changed integral zero agrees with literal evaluation under the fixed comparison. -/
theorem additiveGroupBaseChangeZero_affineSpace (R : CommRingCat.{u}) :
    additiveGroupBaseChangeZero (Spec R) ≫
      (additiveGroupBaseChangeAffineSpaceIso (Spec R)).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
        (polynomialAffineSpaceIso R).hom := by
  apply (AffineSpace.isPullback_map (n := ULift.{u} Unit)
    (specULiftZIsTerminal.from (Spec R))).hom_ext
  · rw [Category.assoc, additiveGroupBaseChangeAffineSpaceIso_hom_map,
      ← Category.assoc, additiveGroupBaseChangeZero_fst,
      Category.assoc, polynomial_zero_affineSpace_map]
  · rw [Category.assoc, additiveGroupBaseChangeAffineSpaceIso_hom_over,
      Category.assoc, polynomialAffineSpaceIso_hom_over]
    change additiveGroupBaseChangeZero (Spec R) ≫ pullback.snd _ _ =
      (Scheme.SmoothSite.Contraction.polynomialAffinePoint R (0 : R)).left ≫
        (Scheme.SmoothSite.Contraction.polynomialAffineLine R).hom
    rw [additiveGroupBaseChangeZero_snd, MorphismProperty.Over.w]
    rfl

/-- The existing native-coordinate zero point is exactly the integral zero pullback lift. -/
theorem polynomial_zero_nativePolynomialAffineLineIso_inv (R : CommRingCat.{u}) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
      (nativePolynomialAffineLineIso R).inv = additiveGroupBaseChangeZero (Spec R) := by
  apply (cancel_mono (additiveGroupBaseChangeAffineSpaceIso (Spec R)).hom).1
  rw [additiveGroupBaseChangeZero_affineSpace]
  simp only [nativePolynomialAffineLineIso, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry
