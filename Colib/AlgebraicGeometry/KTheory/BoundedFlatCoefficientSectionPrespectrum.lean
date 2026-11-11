/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionWaldhausen
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum

/-!
# The joint scheme/coefficient section prespectrum diagram

The same actual sections and strictly zero-preserving exact reindexings define a diagram in
Mathlib's wide subcategory of the native small Waldhausen category. Its prespectrum is the
existing iterated-S construction, with no new perfect-complex realization.
Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSections.lean`,
sectionModel through sectionModelRestriction_app, at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory CategoryTheory.StrictSections
open AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}

/-- The fine section Model retains the original native fiber structure and joint zero. -/
def boundedAboveFlatCoefficientSectionModel (i : Index R) : WideSubcategory preservesZero.{u + 1} :=
  ⟨{ Obj := BoundedAboveFlatCoefficientSections i,
       waldhausen := boundedAboveFlatCoefficientSectionWaldhausen i }⟩

/-- The original exact reindexing is literally zero-preserving in the actual Model category. -/
def boundedAboveFlatCoefficientSectionModelMap {i k : Index R} (f : i ⟶ k) :
    boundedAboveFlatCoefficientSectionModel i ⟶ boundedAboveFlatCoefficientSectionModel k :=
  ⟨⟨boundedAboveFlatCoefficientSectionsMap f, boundedAboveFlatCoefficientSectionsMap_exact f⟩,
    boundedAboveFlatCoefficientSectionsMap_sectionZero f⟩

/-- All original scheme and coefficient maps form one actual strict fine Model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSections.lean:190"
  "adaptation" "Original evaluation-transported structure, exact maps and shared chosen zero"]
def boundedAboveFlatCoefficientSectionModelFunctor (R : CommRingCat.{u}) :
    Index R ⥤ WideSubcategory preservesZero.{u + 1} where
  obj := boundedAboveFlatCoefficientSectionModel
  map := boundedAboveFlatCoefficientSectionModelMap
  map_id i := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact underCocartesianReindex_id (boundedAboveFlatCoefficientProjection R) i
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact underCocartesianReindex_comp (boundedAboveFlatCoefficientProjection R) f g

/-- Apply the original iterated-S realization to the same actual fine Models. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSections.lean:201"
  "adaptation" "Original evaluation-transported structure, exact maps and shared chosen zero"]
def boundedAboveFlatCoefficientSectionPrespectrumFunctor (R : CommRingCat.{u}) :
    Index R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientSectionModelFunctor R ⋙ prespectrumFunctor

/-- The native coefficient Model row of a specified scheme over the unchanged base. -/
def boundedAboveFlatCoefficientSectionModelRow (P : Over (Spec R)) :
    Under R ⥤ WideSubcategory preservesZero.{u + 1} :=
  row P ⋙ boundedAboveFlatCoefficientSectionModelFunctor R

/-- Native scheme restriction uses the same joint zero-preserving Model reindexing. -/
def boundedAboveFlatCoefficientSectionModelRestriction {P Q : Over (Spec R)} (f : P ⟶ Q) :
    boundedAboveFlatCoefficientSectionModelRow Q ⟶ boundedAboveFlatCoefficientSectionModelRow P :=
  Functor.whiskerRight (rowTransformation f) (boundedAboveFlatCoefficientSectionModelFunctor R)

/-- Every native restriction component is the unchanged original joint Model map. -/
theorem boundedAboveFlatCoefficientSectionModelRestriction_app {P Q : Over (Spec R)}
    (f : P ⟶ Q) (a : Under R) :
    (boundedAboveFlatCoefficientSectionModelRestriction f).app a =
      boundedAboveFlatCoefficientSectionModelMap (f.op, 𝟙 a) := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0538"] boundedAboveFlatCoefficientSectionPrespectrumFunctor

end AlgebraicGeometry.Scheme.Modules
