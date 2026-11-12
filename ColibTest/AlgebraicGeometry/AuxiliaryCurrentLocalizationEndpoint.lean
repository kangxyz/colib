module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentLocalization

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
noncomputable section
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

open AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
open ParameterAuxiliarySupport
variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] [CompactSpace T]

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (iteratedLift f.left T (specUnder.obj a)) :=
  iteratedLift_spec_isStableEquivalence f T a

example
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (currentLift f.left T (specUnder.obj a)) :=
  currentLift_spec_isStableEquivalence f T a

example {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] :
    IsStableEquivalence (currentLift f T (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) :=
  currentLift_integer_isStableEquivalence f T

example {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (currentLift f T (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))) :=
  currentLift_integer_signed_isIso f T d

example {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    currentLift f T X ≫ homotopyFiberProjection ((currentRestriction f T).app X) =
      (currentEnlargement f T).app X :=
  currentLift_projection f T X

example {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (T : Q.Opens) [CompactSpace T] (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(k : ℤ) - 1)).map
      (currentLift f T (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))) :=
  currentLift_integer_signed_isIso f T (-(k : ℤ) - 1)
