/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFullOpenBassLocalization
public import Colib.Topology.Prespectrum.FiberLiftConnecting

/-!
# The original auxiliary-supported cone boundary through its specified fiber lift

The existing signed cone boundary equals the intrinsic connecting map of
the same whole-null fiber lift. The proof uses the original cone-to-fiber
connecting equation, without choosing a sign or a new null.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientAuxiliaryFiberConnecting.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The signed cone boundary of the original G7 auxiliary-supported full-open diagram. -/
def boundedFlatCoefficientAuxiliaryLocalizationConnecting (a : Under R) (d : ℤ) :
    stableHomotopyGroup
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) (d + 1) ⟶
      stableHomotopyGroup
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a) d :=
  let := boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence
    f T a (d + 1)
  inv ((stableHomotopyFunctor (d + 1)).map
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a)) ≫
      stableMappingConeConnecting
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence
          f T a) d

/-- The original fine boundary recovers the signed fiber boundary through the same null lift. -/
@[reassoc]
theorem boundedFlatCoefficientAuxiliaryLocalizationConnecting_comp_fiberMap
    (a : Under R) (d : ℤ) :
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a) =
      stableFiberConnecting
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) d := by
  let c := (stableHomotopyFunctor (d + 1)).map
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a)
  let : IsIso c :=
    boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence
      f T a (d + 1)
  unfold boundedFlatCoefficientAuxiliaryLocalizationConnecting
  rw [Category.assoc,
    ← boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_connecting]
  exact IsIso.inv_hom_id_assoc c _

/-- The old cone-defined boundary is precisely the intrinsic boundary of its original lift. -/
theorem boundedFlatCoefficientAuxiliaryLocalizationConnecting_eq_fiberLift
    (a : Under R) (d : ℤ) :
    letI : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f
        T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a))) :=
      boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence
        f T a d
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d =
      stableFiberLiftConnecting
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a) d
          := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f
        T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a))) :=
      boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence
        f T a d
  apply stableFiberLiftConnecting_unique
  exact boundedFlatCoefficientAuxiliaryLocalizationConnecting_comp_fiberMap f T a d

end AlgebraicGeometry.Scheme.Modules

