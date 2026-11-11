module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportModels
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (a : Under R) : WideSubcategory preservesZero.{u + 1} :=
  boundedAboveFlatCoefficientSupportedModel f a

example {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientSupportedModel f a ⟶
      boundedAboveFlatCoefficientSupportedModel f b :=
  boundedAboveFlatCoefficientSupportedModelMap f g

example : Under R ⥤ WideSubcategory preservesZero.{u + 1} :=
  boundedAboveFlatCoefficientSupportedModelFunctor f

example : boundedAboveFlatCoefficientSupportedModelFunctor f ⟶
    boundedAboveFlatCoefficientSectionModelRow Q :=
  boundedAboveFlatCoefficientSupportedForgetModelTransformation f

example : boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⟶
    boundedAboveFlatCoefficientAmbientPrespectrumFunctor Q :=
  boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f
