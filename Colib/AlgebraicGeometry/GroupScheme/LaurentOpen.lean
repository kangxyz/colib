/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Additive
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The positive Laurent open and its native coordinates

The schemes in this file are Stacks' existing additive and multiplicative group schemes.
Their underlying schemes are the affine line and its positive Laurent open. Their base changes
remain the existing native pullbacks, and the coordinate is the forward Laurent unit `T`.
The open immersion is a morphism of schemes, not a homomorphism of group schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- The positive Laurent open, on the existing integral native schemes. -/
def multiplicativeGroupToAdditive : multiplicativeGroupULift.{u} ⟶ additiveGroup.{u} :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

instance : IsOpenImmersion multiplicativeGroupToAdditive.{u} :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial (ULift.{u} ℤ))

/-- The Laurent open preserves the original structure morphisms to the integral base. -/
@[reassoc]
theorem multiplicativeGroupToAdditive_over :
    multiplicativeGroupToAdditive.{u} ≫
        (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) =
      (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ))) := by
  change Spec.map (CommRingCat.ofHom Polynomial.toLaurent) ≫
    Spec.map (CommRingCat.ofHom Polynomial.C) =
      Spec.map (CommRingCat.ofHom LaurentPolynomial.C)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Polynomial.toLaurent_C r

/-- Restricting the polynomial coordinate gives the forward Laurent unit, not its inverse. -/
theorem multiplicativeGroupToAdditive_appTop_coordinate :
    multiplicativeGroupToAdditive.{u}.appTop additiveCoordinate =
      (multiplicativeCoordinate : (Γ(multiplicativeGroupULift.{u}, ⊤))ˣ).val := by
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Polynomial.toLaurent :
      Polynomial (ULift.{u} ℤ) →+* LaurentPolynomial (ULift.{u} ℤ)))
  have hX := congrArg (fun f => f.hom Polynomial.X) h
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv.hom
      (Polynomial.toLaurent Polynomial.X) =
    (Spec.map (CommRingCat.ofHom Polynomial.toLaurent)).appTop.hom
      ((Scheme.ΓSpecIso (.of (Polynomial (ULift.{u} ℤ)))).inv.hom Polynomial.X) at hX
  simpa only [Polynomial.toLaurent_X,
    multiplicativeGroupToAdditive, additiveCoordinate, multiplicativeCoordinate,
    IsUnit.unit_spec] using hX.symm

/-- The actual base change of the positive Laurent open over an arbitrary scheme. -/
def multiplicativeGroupBaseChangeToAdditive (X : Scheme.{u}) :
    multiplicativeGroupBaseChange X ⟶ additiveGroupBaseChange X :=
  pullback.map _ _ _ _ multiplicativeGroupToAdditive (𝟙 X) (𝟙 _)
    (by simpa using multiplicativeGroupToAdditive_over.symm) (by simp)

instance (X : Scheme.{u}) : IsOpenImmersion (multiplicativeGroupBaseChangeToAdditive X) := by
  unfold multiplicativeGroupBaseChangeToAdditive
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion multiplicativeGroupToAdditive.{u})
    (inferInstance : IsOpenImmersion (𝟙 X))
    multiplicativeGroupToAdditive_over.symm (by simp)

/-- The positive open retains the native projection to the integral affine line. -/
@[reassoc]
theorem multiplicativeGroupBaseChangeToAdditive_fst (X : Scheme.{u}) :
    multiplicativeGroupBaseChangeToAdditive X ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ multiplicativeGroupToAdditive := by
  simp [multiplicativeGroupBaseChangeToAdditive]

/-- The positive open is over the original base scheme. -/
@[reassoc]
theorem multiplicativeGroupBaseChangeToAdditive_snd (X : Scheme.{u}) :
    multiplicativeGroupBaseChangeToAdditive X ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  simp [multiplicativeGroupBaseChangeToAdditive]

/-- The polynomial coordinate on the existing native affine-line base change. -/
def additiveGroupBaseChangeCoordinate (X : Scheme.{u}) :
    Γ(additiveGroupBaseChange X, ⊤) :=
  (pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from X)).appTop additiveCoordinate

/-- The forward Laurent unit on the existing native multiplicative-group base change. -/
def multiplicativeGroupBaseChangeCoordinate (X : Scheme.{u}) :
    (Γ(multiplicativeGroupBaseChange X, ⊤))ˣ :=
  multiplicativeGroupPointUnit
    (pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from X))

/-- Base change preserves the actual polynomial-coordinate/forward-unit equality. -/
@[colib_tag "COL-0298"]
theorem multiplicativeGroupBaseChangeToAdditive_appTop_coordinate (X : Scheme.{u}) :
    (multiplicativeGroupBaseChangeToAdditive X).appTop
        (additiveGroupBaseChangeCoordinate X) =
      (multiplicativeGroupBaseChangeCoordinate X).val := by
  have h := congrArg (fun f => f.appTop)
    (multiplicativeGroupBaseChangeToAdditive_fst X)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  have he := ConcreteCategory.congr_hom h additiveCoordinate
  change (multiplicativeGroupBaseChangeToAdditive X).appTop
      (additiveGroupBaseChangeCoordinate X) =
    (pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from X)).appTop
      (multiplicativeGroupToAdditive.appTop additiveCoordinate) at he
  rw [multiplicativeGroupToAdditive_appTop_coordinate] at he
  exact he

end AlgebraicGeometry
