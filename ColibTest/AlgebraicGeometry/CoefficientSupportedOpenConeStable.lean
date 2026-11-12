module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenConeStable

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Waldhausen.IteratedS
noncomputable section
universe u

variable {E F G : LoopPrespectrum.{u}} (r : E ⟶ F) (q : F ⟶ G)
  (N : Homotopy (r ≫ q) (zeroHom E G))

example
    (he : IsStableEquivalence (mappingConeFiberComparison r))
    (hi : ∀ d : ℤ, Function.Injective ((stableHomotopyFunctor d).map r))
    (hs : ∀ d : ℤ, d ≠ 0 → Function.Surjective ((stableHomotopyFunctor d).map r))
    (hg : ∀ d : ℤ, d ≠ 0 → Subsingleton (stableHomotopyGroup G d))
    (hzero : Function.Bijective ((stableHomotopyFunctor 0).map (mappingConeDesc r q N))) :
    IsStableEquivalence (mappingConeDesc r q N) :=
  mappingConeDesc_isStableEquivalence_of_cofinality r q N he hi hs hg hzero

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
  [CompactSpace P.left] [CompactSpace Q.left]

example (a : Under R)
    (N : Homotopy
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a)
      (zeroHom ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)
        ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a))) :
    Function.Bijective ((stableHomotopyFunctor 0).map
      (mappingConeDesc
        ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
        f T).app a)
        ((boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a) N))
          :=
  boundedAboveFlatCoefficientSupportedOpenConeDesc_stable_zero_bijective f T a N

example (a : Under R) :
    mappingConeInclusion
        ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a) ≫
        boundedAboveFlatCoefficientSupportedOpenGradingConeComparison f T a =
      (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a :=
  boundedAboveFlatCoefficientSupportedOpenGradingConeComparison_inclusion f T a

example (a : Under R)
    (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    (boundedAboveFlatCoefficientSupportedOpenGradingConeComparison f T a).map n
      (ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).point n)
        (((boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T).obj a).point n)
        (((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
          f T).app a).map n)
        (s, x)) =
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s, x)
        :=
  boundedAboveFlatCoefficientSupportedOpenGradingConeComparison_cylinder f T a n s x

example (a : Under
  R) :
    (boundedAboveFlatCoefficientSupportedOpenGradingConeComparisonTransformation f T).app a =
      boundedAboveFlatCoefficientSupportedOpenGradingConeComparison f T a :=
  boundedAboveFlatCoefficientSupportedOpenGradingConeComparisonTransformation_app f T a

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

example (a : Under R) (d : ℤ) :
    Function.Injective ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a))
        :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_stable_injective f T a d

example
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Function.Surjective ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a))
        :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_stable_surjective_of_ne_zero f T a d hd

example (a : Under R)
    (N : Homotopy
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a)
      (zeroHom ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)
        ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a))) :
    IsStableEquivalence
      (mappingConeDesc
        ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
        f T).app a)
        ((boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a) N)
          :=
  boundedAboveFlatCoefficientSupportedOpenConeDesc_isStableEquivalence f T a N

example (a :
  Under R) :
    IsStableEquivalence (boundedAboveFlatCoefficientSupportedOpenGradingConeComparison f T a) :=
  boundedAboveFlatCoefficientSupportedOpenGradingConeComparison_isStableEquivalence f T a

