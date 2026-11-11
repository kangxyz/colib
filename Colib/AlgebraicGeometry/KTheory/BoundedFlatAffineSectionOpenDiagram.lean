/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenCoefficientModel
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.AffineBaseChange

/-!
# The original fixed-open relative coefficient diagram

Each algebra uses the specified pullback of the fixed original open. The unchanged exact
section reindexing forms a strict Model diagram and hence an actual strict prespectrum diagram.
The original fine-to-coarse maps give a literal natural transformation on that same diagram.
The identity-algebra object remains its actual pullback, rather than being identified with j.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.StrictSections CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The relative-open section Models on the fixed original pullbacks form a strict diagram. -/
def boundedAboveFlatAffineSectionOpenModelFunctor :
    Under R ⥤ WideSubcategory preservesZero.{u + 1} where
  obj a := boundedAboveFlatAffineSectionOpenModel (inclusion j a)
  map {a b} f := boundedAboveFlatAffineSectionOpenReindexModelMap
    (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f)
  map_id a := by
    apply WideSubcategory.hom_ext
    apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatAffineSectionsMap_id a.right
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatAffineSectionsMap_comp f.right g.right

/-- The original iterated-S prespectrum functor applied to the genuine coarse section diagram. -/
def boundedAboveFlatAffineSectionOpenPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatAffineSectionOpenModelFunctor j ⋙ prespectrumFunctor

/-- Each coefficient arrow is exactly the original relative-open reindexing map. -/
theorem boundedAboveFlatAffineSectionOpenPrespectrumFunctor_map {a b : Under R} (f : a ⟶ b) :
    (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map f =
      boundedAboveFlatAffineSectionOpenReindexPrespectrumMap
        (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f) := rfl

/-- Changing the weak class on the same sections is strictly natural on the fixed-open diagram. -/
def boundedAboveFlatAffineSectionOpenModelTransformation :
    Under.forget R ⋙ boundedAboveFlatAffineSectionModelFunctor ⟶
      boundedAboveFlatAffineSectionOpenModelFunctor j where
  app a := boundedAboveFlatAffineSectionOpenModelMap (inclusion j a)
  naturality _ _ f := boundedAboveFlatAffineSectionOpenModelMap_naturality
    (inclusion j _) (inclusion j _) f.right (openMap j f) (openMap_inclusion j f)

/-- Original realization retains the same fine-to-coarse natural transformation. -/
def boundedAboveFlatAffineSectionOpenPrespectrumTransformation :
    Under.forget R ⋙ boundedAboveFlatAffineSectionPrespectrumFunctor ⟶
      boundedAboveFlatAffineSectionOpenPrespectrumFunctor j :=
  Functor.whiskerRight (boundedAboveFlatAffineSectionOpenModelTransformation j) prespectrumFunctor

/-- Every component is the unchanged fine-to-relative-open section map. -/
theorem boundedAboveFlatAffineSectionOpenPrespectrumTransformation_app (a : Under R) :
    (boundedAboveFlatAffineSectionOpenPrespectrumTransformation j).app a =
      boundedAboveFlatAffineSectionOpenPrespectrumMap (inclusion j a) := rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionOpenDiagram.lean:29-67"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineSectionOpenModelFunctor
  boundedAboveFlatAffineSectionOpenPrespectrumFunctor
  boundedAboveFlatAffineSectionOpenPrespectrumFunctor_map
  boundedAboveFlatAffineSectionOpenModelTransformation
  boundedAboveFlatAffineSectionOpenPrespectrumTransformation
  boundedAboveFlatAffineSectionOpenPrespectrumTransformation_app

end AlgebraicGeometry.Scheme.Modules
