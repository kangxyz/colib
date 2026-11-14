/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFineLocalizationBoundary
public import Colib.Topology.Prespectrum.FiberLiftConnecting

/-!
# The original fine boundary through its specified fiber lift

The existing signed cone boundary equals the intrinsic connecting map of
the same whole-null fiber lift. The proof uses the original cone-to-fiber
connecting equation, without choosing a sign or a new null.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The original fine boundary recovers the signed fiber boundary through the same null lift. -/
@[reassoc]
theorem boundedAboveFlatCoefficientFineLocalizationConnecting_comp_fiberMap
    (a : Under R) (d : ℤ) :
    boundedAboveFlatCoefficientFineLocalizationConnecting f a d ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a) =
      stableFiberConnecting
        ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a) d := by
  let c := (stableHomotopyFunctor (d + 1)).map
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)
  let : IsIso c :=
    boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence
      f a (d + 1)
  unfold boundedAboveFlatCoefficientFineLocalizationConnecting
  rw [Category.assoc,
    ← boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_connecting]
  exact IsIso.inv_hom_id_assoc c _

/-- The old cone-defined boundary is precisely the intrinsic boundary of its original lift. -/
theorem boundedAboveFlatCoefficientFineLocalizationConnecting_eq_fiberLift
    (a : Under R) (d : ℤ) :
    letI : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a))) :=
      boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a d
    boundedAboveFlatCoefficientFineLocalizationConnecting f a d =
      stableFiberLiftConnecting
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a) d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a))) :=
      boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a d
  apply stableFiberLiftConnecting_unique
  exact boundedAboveFlatCoefficientFineLocalizationConnecting_comp_fiberMap f a d

end AlgebraicGeometry.Scheme.Modules

