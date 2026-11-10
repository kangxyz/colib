/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionDiagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionPrespectrum

/-!
# The original support-forgetting Model and prespectrum maps

The actual full-subcategory inclusion is exact and preserves the chosen section zero literally.
The original coefficient forget squares therefore give a strict natural transformation from
the fixed-open supported diagram to the ambient section diagram restricted along Under.forget.
This is an inclusion toward localization, with no equivalence or localization assertion.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original support-forgetting functor with its proved exactness and literal chosen zero. -/
def boundedAboveFlatAffineSupportedSectionForgetModelMap :
    boundedAboveFlatAffineSupportedSectionModel j ⟶ boundedAboveFlatAffineSectionModel R :=
  ⟨⟨(boundedAboveFlatAffineSectionSupported j).ι,
    boundedAboveFlatAffineSupportedSectionForget_exact j⟩,
    boundedAboveFlatAffineSupportedSectionForget_zero j⟩

/-- Forgetting support commutes with each original specified coefficient/open-pair square. -/
theorem boundedAboveFlatAffineSupportedSectionForgetModelMap_naturality
    {S : CommRingCat.{u}} {V : Scheme.{u}} (j' : V ⟶ Spec S) [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedAboveFlatAffineSupportedSectionModelMap j j' f l h ≫
        boundedAboveFlatAffineSupportedSectionForgetModelMap j' =
      boundedAboveFlatAffineSupportedSectionForgetModelMap j ≫
        boundedAboveFlatAffineSectionModelMap f := by
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  exact boundedAboveFlatAffineSupportedSectionsMap_forget j j' f l h

/-- Actual support inclusion is strictly natural on the original fixed-pullback diagram. -/
def boundedAboveFlatAffineSupportedSectionForgetModelTransformation :
    boundedAboveFlatAffineSupportedSectionModelFunctor j ⟶
      Under.forget R ⋙ boundedAboveFlatAffineSectionModelFunctor where
  app a := boundedAboveFlatAffineSupportedSectionForgetModelMap (inclusion j a)
  naturality _ _ f := boundedAboveFlatAffineSupportedSectionForgetModelMap_naturality
    (inclusion j _) (inclusion j _) f.right (openMap j f) (openMap_inclusion j f)

/-- The actual iterated-S support-forgetting prespectrum arrow. -/
def boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap :
    prespectrum (boundedAboveFlatAffineSupportedSectionModel j) ⟶
      prespectrum (boundedAboveFlatAffineSectionModel R) :=
  prespectrumMap (boundedAboveFlatAffineSupportedSectionForgetModelMap j)

/-- Apply the original prespectrum functor to the actual strict Model natural transformation. -/
def boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation :
    boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j ⟶
      Under.forget R ⋙ boundedAboveFlatAffineSectionPrespectrumFunctor :=
  Functor.whiskerRight (boundedAboveFlatAffineSupportedSectionForgetModelTransformation j)
    prespectrumFunctor

/-- Its components are exactly the original support-forgetting iterated-S maps. -/
theorem boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation_app (a : Under R) :
    (boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j).app a =
      boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a) := rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionForgetModel.lean:29-69"
  "adaptation"
  "Actual support inclusion and strict fixed-base Waldhausen-model and prespectrum transformation"]
  boundedAboveFlatAffineSupportedSectionForgetModelMap
  boundedAboveFlatAffineSupportedSectionForgetModelMap_naturality
  boundedAboveFlatAffineSupportedSectionForgetModelTransformation
  boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap
  boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation
  boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation_app

end AlgebraicGeometry.Scheme.Modules
