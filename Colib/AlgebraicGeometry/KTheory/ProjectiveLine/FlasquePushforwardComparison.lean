/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasquePushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence

/-! # Direct image on bounded-below flasque perfect representatives

The ordinary direct-image complex computes the canonical derived direct image
on a bounded-below flasque complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local notation "F" => (Functor.mapHomologicalComplex (pushforward f) (ComplexShape.up ℤ))

/-- Flasque terms are acyclic for the literal direct-image functor. -/
theorem pushforward_rightAcyclic_of_flasque (M : X.Modules)
    (hM : TopCat.Sheaf.IsFlasque ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M)) :
    (pushforward f).rightAcyclic M := by
  let : TopCat.Sheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj M) := hM
  have hfin : PreservesFiniteLimits (pushforward f) := inferInstance
  refine (((pushforward f).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus M).2 hfin).mpr
    fun i hi => ?_
  exact Stacks.Cohomology.FlasquePushforward.isZero_rightDerivedPlus_modulePushforward_of_isFlasque
    f.toLRSHom.toShHom M i hi

/-- The derived-unit component is invertible on a bounded-below flasque representative. -/
theorem isIso_flasquePushforwardUnit_app [QuasiCompact f] [QuasiSeparated f]
    (K : CochainComplex X.Modules ℤ) (hK : CochainComplex.plus X.Modules K)
    (hfl : ∀ n, TopCat.Sheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj (K.X n))) :
    IsIso ((derivedPushforwardModulesUnit f).app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) :=
  Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic (pushforward f)
    (derivedPushforwardModules f) (derivedPushforwardModulesUnit f) K hK
    (fun n => pushforward_rightAcyclic_of_flasque f (K.X n) (hfl n))

/-- The canonical comparison identifies the actual bounded-below direct-image complex. -/
def flasquePushforwardIso [QuasiCompact f] [QuasiSeparated f]
    (K : CochainComplex X.Modules ℤ) (hK : CochainComplex.plus X.Modules K)
    (hfl : ∀ n, TopCat.Sheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj (K.X n))) :
    DerivedCategory.Q.obj ((F).obj K) ≅
      (derivedPushforwardModules f).obj (DerivedCategory.Q.obj K) := by
  let c := ComplexShape.up ℤ
  let qX := HomotopyCategory.quotient X.Modules c
  let R := derivedPushforwardModules f
  let α := derivedPushforwardModulesUnit f
  let : IsIso (α.app (qX.obj K)) := isIso_flasquePushforwardUnit_app f K hK hfl
  exact ((DerivedCategory.quotientCompQhIso Y.Modules).app ((F).obj K)).symm ≪≫
    DerivedCategory.Qh.mapIso (((pushforward f).mapHomotopyCategoryFactors c).app K).symm ≪≫
    asIso (α.app (qX.obj K)) ≪≫
    R.mapIso ((DerivedCategory.quotientCompQhIso X.Modules).app K)

/-- Direct image preserves a short exact sequence when its first two terms are flasque. -/
theorem pushforward_shortExact_of_flasque (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : TopCat.Sheaf.IsFlasque ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₁))
    (h₂ : TopCat.Sheaf.IsFlasque ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂)) :
    (S.map (pushforward f)).ShortExact :=
  ((pushforward f).rightAcyclic_and_shortExact_map_of_shortExact S hS).2.1
    (pushforward_rightAcyclic_of_flasque f S.X₁ h₁)
    (pushforward_rightAcyclic_of_flasque f S.X₂ h₂) |>.2

end AlgebraicGeometry.Scheme.Modules
