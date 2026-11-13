module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenSections
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Topology Topology.LoopPrespectrum
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
example (a : Under R) : WideSubcategory preservesZero.{u + 1} :=
  boundedAboveFlatCoefficientOpenModel f a
example {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatCoefficientOpenModel f a ⟶ boundedAboveFlatCoefficientOpenModel f b :=
  boundedAboveFlatCoefficientOpenModelMap f g
example : Under R ⥤ WideSubcategory preservesZero.{u + 1} :=
  boundedAboveFlatCoefficientOpenModelFunctor f
example : boundedAboveFlatCoefficientOpenModelFunctor f ⟶
    boundedAboveFlatCoefficientFullOpenModelFunctor f :=
  boundedAboveFlatCoefficientOpenRestrictionModelTransformation f
example : boundedAboveFlatCoefficientSectionModelRow Q ⟶
    boundedAboveFlatCoefficientOpenModelFunctor f :=
  boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f
example : boundedAboveFlatCoefficientOpenPrespectrumFunctor f ⟶
    boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f :=
  boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f
