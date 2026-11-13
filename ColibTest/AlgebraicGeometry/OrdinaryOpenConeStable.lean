module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenConeStable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (a : Under R)
example (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedAboveFlatCoefficientGradedOpenModel f a)) d) :=
  boundedAboveFlatCoefficientGradedOpen_stable_subsingleton f a d hd
variable [CompactSpace P.left] [CompactSpace Q.left]
example :
    (boundedAboveFlatCoefficientOpenConeComparisonTransformation f).app a =
      boundedAboveFlatCoefficientOpenConeComparison f a :=
  boundedAboveFlatCoefficientOpenConeComparisonTransformation_app f a
example (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    (boundedAboveFlatCoefficientOpenConeComparison f a).map n
      (ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).point n)
        (((boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f).obj a).point n)
        (((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a).map n)
        (s, x)) =
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x) :=
  boundedAboveFlatCoefficientOpenConeComparison_cylinder f a n s x
variable [QuasiSeparatedSpace Q.left]
example (N : Homotopy
    ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a ≫
      (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a)
    (zeroHom ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a)
      ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a))) :
    IsStableEquivalence
      (mappingConeDesc
        ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a) N) :=
  boundedAboveFlatCoefficientOpenConeDesc_isStableEquivalence f a N
example : IsStableEquivalence (boundedAboveFlatCoefficientOpenConeComparison f a) :=
  boundedAboveFlatCoefficientOpenConeComparison_isStableEquivalence f a
