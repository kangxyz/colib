/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.Smooth
public import Colib.AlgebraicGeometry.Sites.Smooth.Basic

/-!
# Native additive and multiplicative groups on the smooth site

The objects are exactly the existing Stacks base-change schemes, with their
literal second pullback projections. The morphism is Colib's existing positive
Laurent open and retains the forward Laurent coordinate, not its inverse.

Adapted from motivic_source_a6805c4, the smooth Torus/Basic and AffineLine/Laurent
owners, using the native model already chosen in Colib.GroupScheme.LaurentOpen.
No geometric contraction or homotopy-invariance assertion is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The existing native additive-group base change as a smooth-site object. -/
def additiveGroupObject (S : Scheme.{u}) : SmoothSite S :=
  mk (pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from S))

/-- The existing native multiplicative-group base change as a smooth-site object. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Torus/Basic.lean:33-44"
  "adaptation" "Native Stacks multiplicative base change, over an arbitrary scheme"]
def multiplicativeGroupObject (S : Scheme.{u}) : SmoothSite S :=
  mk (pullback.snd (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from S))

@[simp]
theorem additiveGroupObject_left (S : Scheme.{u}) :
    (additiveGroupObject S).left = additiveGroupBaseChange S := rfl

@[simp]
theorem multiplicativeGroupObject_left (S : Scheme.{u}) :
    (multiplicativeGroupObject S).left = multiplicativeGroupBaseChange S := rfl

/-- The actual positive Laurent open as a morphism of the smooth site. -/
def multiplicativeGroupOpen (S : Scheme.{u}) :
    multiplicativeGroupObject S ⟶ additiveGroupObject S :=
  homMk (multiplicativeGroupBaseChangeToAdditive S)
    (multiplicativeGroupBaseChangeToAdditive_snd S)

@[simp]
theorem multiplicativeGroupOpen_left (S : Scheme.{u}) :
    (multiplicativeGroupOpen S).left = multiplicativeGroupBaseChangeToAdditive S := rfl

instance (S : Scheme.{u}) : IsOpenImmersion (multiplicativeGroupOpen S).left :=
  inferInstanceAs (IsOpenImmersion (multiplicativeGroupBaseChangeToAdditive S))

/-- The native open retains exactly the original forward Laurent coordinate. -/
theorem multiplicativeGroupOpen_appTop_coordinate (S : Scheme.{u}) :
    (multiplicativeGroupOpen S).left.appTop (additiveGroupBaseChangeCoordinate S) =
      (multiplicativeGroupBaseChangeCoordinate S).val :=
  multiplicativeGroupBaseChangeToAdditive_appTop_coordinate S

end AlgebraicGeometry.Scheme.SmoothSite
