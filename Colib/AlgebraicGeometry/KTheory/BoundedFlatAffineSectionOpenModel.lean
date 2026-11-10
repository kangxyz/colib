/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenStructure
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionPrespectrum

/-! # Actual relative-open section model and unchanged fine-to-coarse map

Only weakness changes, through actual original evaluation and open restriction.
The section category, cofibrations and chosen zero are retained.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original section category with its actual relative-open weak class and original zero. -/
def boundedAboveFlatAffineSectionOpenModel : WideSubcategory preservesZero.{u + 1} :=
  ⟨{ Obj := BoundedAboveFlatAffineSections R,
     waldhausen := boundedAboveFlatAffineSectionOpenWaldhausen j }⟩

/-- The identity section functor changes only the weak class, retaining the chosen zero. -/
def boundedAboveFlatAffineSectionOpenModelMap :
    boundedAboveFlatAffineSectionModel R ⟶ boundedAboveFlatAffineSectionOpenModel j :=
  ⟨⟨𝟭 _, changeWeak_exact (boundedAboveFlatAffineSectionOpenNested j)⟩, rfl⟩

/-- The original fine section prespectrum maps to the actual relative-open section prespectrum. -/
def boundedAboveFlatAffineSectionOpenPrespectrumMap :
    boundedAboveFlatAffineSectionPrespectrumFunctor.obj R ⟶
      prespectrum (boundedAboveFlatAffineSectionOpenModel j) :=
  prespectrumMap (boundedAboveFlatAffineSectionOpenModelMap j)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionOpenNull.lean:38-52"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineSectionOpenModel
  boundedAboveFlatAffineSectionOpenModelMap
  boundedAboveFlatAffineSectionOpenPrespectrumMap

end AlgebraicGeometry.Scheme.Modules
