module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedStableGroups

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example (a : Under R) (n : ℕ) :
    Subsingleton ((boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.K
      (n + 1)) :=
  boundedAboveFlatCoefficientSupportedGradedOpen_K_succ_subsingleton f T a n

example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).coarseStructure.K 0 →*
      Multiplicative (BoundedAboveFlatCoefficientSupportedOpenImageQuotient f T a) :=
  boundedAboveFlatCoefficientSupportedOpenKZeroValueMap f T a

example (a : Under R) :
    Function.Injective (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap f T a) :=
  boundedAboveFlatCoefficientSupportedOpenKZeroValueMap_injective f T a

example (a : Under R) (n : ℕ) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a))
      ((n + 1 : ℕ) : ℤ)) :=
  boundedAboveFlatCoefficientSupportedGradedOpen_stable_succ_subsingleton f T a n

example (a : Under R) (k : ℕ) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a))
      (-(Int.ofNat k + 1))) :=
  boundedAboveFlatCoefficientSupportedGradedOpen_stable_neg_subsingleton f T a _ (by
    have hk : (0 : ℤ) ≤ Int.ofNat k := Int.natCast_nonneg k
    omega)

example (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedAboveFlatCoefficientSupportedGradedOpenModel f T a)) d) :=
  boundedAboveFlatCoefficientSupportedGradedOpen_stable_subsingleton f T a d hd
