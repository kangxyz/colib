/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.LaurentComplement
public import Colib.AlgebraicGeometry.Scheme.CartesianRange

/-!
# Base change of the actual integral zero and Laurent complement

The schemes and the Laurent map are the native Stacks base changes already
used in Colib. The zero map is the literal pullback lift of evaluation at zero.
No choice of another line, torus, coordinate, or complementary open is involved.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry

/-- Literal polynomial evaluation at zero, before base change. -/
abbrev integralAdditiveZero : Spec (.of (ULift.{u} ℤ)) ⟶ additiveGroup.{u} :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))

@[reassoc (attr := simp)]
theorem integralAdditiveZero_over :
    integralAdditiveZero.{u} ≫ (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : ULift.{u} ℤ →+* Polynomial (ULift.{u} ℤ)) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : ULift.{u} ℤ)) = 𝟙 _ := by
    ext r
    exact Polynomial.eval_C
  rw [h, Spec.map_id]

/-- The literal integral zero section, pulled back to the existing native line. -/
def additiveGroupBaseChangeZero (S : Scheme.{u}) : S ⟶ additiveGroupBaseChange S :=
  pullback.lift (specULiftZIsTerminal.from S ≫ integralAdditiveZero) (𝟙 S) (by simp)

@[reassoc (attr := simp)]
theorem additiveGroupBaseChangeZero_fst (S : Scheme.{u}) :
    additiveGroupBaseChangeZero S ≫ pullback.fst _ _ =
      specULiftZIsTerminal.from S ≫ integralAdditiveZero :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem additiveGroupBaseChangeZero_snd (S : Scheme.{u}) :
    additiveGroupBaseChangeZero S ≫ pullback.snd _ _ = 𝟙 S :=
  pullback.lift_snd _ _ _

/-- The zero-section square is the full scheme base change, not just a range equation. -/
theorem additiveGroupBaseChangeZero_isPullback (S : Scheme.{u}) :
    IsPullback (additiveGroupBaseChangeZero S) (specULiftZIsTerminal.from S)
      (pullback.fst _ _) integralAdditiveZero := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S))
    (h₂₂ := additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
    (v₁₃ := specULiftZIsTerminal.from S)
  · rw [additiveGroupBaseChangeZero_snd, integralAdditiveZero_over]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · exact additiveGroupBaseChangeZero_fst S
  · exact (IsPullback.of_hasPullback _ _).flip

/-- The existing native positive Laurent map is the full base change of its integral map. -/
theorem multiplicativeGroupBaseChangeToAdditive_isPullback (S : Scheme.{u}) :
    IsPullback (multiplicativeGroupBaseChangeToAdditive S)
      (pullback.fst (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S))
      (pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S)) multiplicativeGroupToAdditive := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S))
    (h₂₂ := additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
    (v₁₃ := specULiftZIsTerminal.from S)
  · rw [multiplicativeGroupBaseChangeToAdditive_snd, multiplicativeGroupToAdditive_over]
    exact (IsPullback.of_hasPullback _ _).flip
  · exact multiplicativeGroupBaseChangeToAdditive_fst S
  · exact (IsPullback.of_hasPullback _ _).flip

/-- Base change preserves the whole actual zero/Laurent complement. -/
theorem range_additiveGroupBaseChangeZero (S : Scheme.{u}) :
    Set.range (additiveGroupBaseChangeZero S) =
      (Set.range (multiplicativeGroupBaseChangeToAdditive S))ᶜ := by
  rw [Scheme.range_fst_of_isPullback (additiveGroupBaseChangeZero_isPullback S),
    Scheme.range_fst_of_isPullback
      (multiplicativeGroupBaseChangeToAdditive_isPullback S),
    range_integral_zero_eq_compl_multiplicativeGroupToAdditive, Set.preimage_compl]

end AlgebraicGeometry
