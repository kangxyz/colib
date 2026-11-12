/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryBasicCurrent
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIntrinsicConnecting
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIntrinsicConnecting

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryBasicConnecting.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The original auxiliary and basic boundaries under actual support forgetting -/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The same original selected-zero null preserves the existing intrinsic signed boundaries. -/
@[reassoc]
theorem current_auxiliary_basic_connecting
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    ParameterAuxiliaryCurrentFiber.currentConnecting f T a d ≫
        (stableHomotopyFunctor d).map ((currentToBasic f.left T).app (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          ((currentOpenForget f.left T).app (specUnder.obj a)) ≫
        ParameterFullCurrentNull.currentConnecting f a d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((currentRestriction f.left T).app (specUnder.obj a))
        ((currentEnlargement f.left T).app (specUnder.obj a))
        ((currentNull f.left T).homotopy (specUnder.obj a)))) :=
    ParameterAuxiliaryCurrentFiber.currentLift_spec_isStableEquivalence f T a d
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((ParameterFullCurrentNull.currentOpen f.left).app (specUnder.obj a))
        ((ParameterFullCurrentNull.currentForget f.left).app (specUnder.obj a))
        ((ParameterFullCurrentNull.currentNull f.left).homotopy (specUnder.obj a)))) :=
    ParameterFullCurrentNull.currentLift_spec_isStableEquivalence f a d
  exact stableFiberLiftConnecting_naturality
    ((currentEnlargement f.left T).app (specUnder.obj a))
    ((currentRestriction f.left T).app (specUnder.obj a))
    ((ParameterFullCurrentNull.currentForget f.left).app (specUnder.obj a))
    ((ParameterFullCurrentNull.currentOpen f.left).app (specUnder.obj a))
    ((currentNull f.left T).homotopy (specUnder.obj a))
    ((ParameterFullCurrentNull.currentNull f.left).homotopy (specUnder.obj a))
    ((currentToBasic f.left T).app (specUnder.obj a))
    ((currentAmbientForget T).app (specUnder.obj a))
    ((currentOpenForget f.left T).app (specUnder.obj a))
    (NatTrans.congr_app (currentEnlargement_basic_square f.left T) (specUnder.obj a))
    (NatTrans.congr_app (currentRestriction_basic_square f.left T) (specUnder.obj a)).symm
    (currentNull_basic_square f.left T (specUnder.obj a)) d

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
