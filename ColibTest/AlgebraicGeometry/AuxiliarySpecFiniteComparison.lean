module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterFiniteComparison

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
noncomputable section
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

example (R : CommRingCat.{u}) (c : Index R)
    {U : Scheme.{u}} (j : U ⟶ space c) [IsOpenImmersion j] :
    IsStableEquivalence (prespectrumMap (supportedRestrictionModel R c j)) :=
  supportedRestriction_stable R c j

example
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (prespectrumMap (ambientComponent Q T a)) :=
  ambientComponent_stable Q T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (prespectrumMap (fiberComponent f T a)) :=
  fiberComponent_stable f T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (prespectrumMap (openComponent f T a)) :=
  openComponent_stable f T a

example
    (S : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤
      Arrow (Arrow (Under (CommRingCat.of (ULift.{u} ℤ)))))
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)).app a) :=
  fiberComparison_iterate_stable f T S i a

example
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)
    (S : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤
      Arrow (Arrow (Under (CommRingCat.of (ULift.{u} ℤ)))))
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor)).app a) :=
  ambientComparison_iterate_stable Q T S i a

example
    (S : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤
      Arrow (Arrow (Under (CommRingCat.of (ULift.{u} ℤ)))))
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (((strictDiagramIterate S i).map
      (Functor.whiskerRight (openComparison f T) prespectrumFunctor)).app a) :=
  openComparison_iterate_stable f T S i a

example
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fiberFiniteComparison f T i).app a) :=
  fiberFiniteComparison_stable f T i a

example (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((ambientFiniteComparison Q T i).app a) :=
  ambientFiniteComparison_stable Q T i a

example
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((openFiniteComparison f T i).app a) :=
  openFiniteComparison_stable f T i a

example (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(k : ℤ) - 1)).map
      ((fiberFiniteComparison f T i).app a)) :=
  fiberFiniteComparison_stable f T i a (-(k : ℤ) - 1)
