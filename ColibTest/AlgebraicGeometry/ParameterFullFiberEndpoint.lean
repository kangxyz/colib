module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentFullFiber
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
noncomputable section
universe u
example {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] :
    IsStableEquivalence (currentLift f (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) :=
  currentLift_integer_isStableEquivalence f
example {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (currentLift f (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))) :=
  currentLift_integer_signed_isIso f d
