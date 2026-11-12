/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalCoefficientRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenSections
public import Colib.KTheory.Waldhausen.Iterated.InverseImageModelDiagram
/-! # Original coarse-open global sections

The coefficient restriction detects the original coarse weak class on the same global
section objects, cofibrations and chosen zero. Both actual arrows retain their strict square.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionModelFunctor
  boundedAboveFlatCoefficientSectionWaldhausen
  boundedAboveFlatCoefficientOriginalEvaluation
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Actual original restriction followed by the existing coarse change of weakness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:35"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
def openSourceTransformation :
    globalRow Q ⟶ boundedAboveFlatCoefficientOpenModelFunctor f :=
  rowRestriction Q ≫ boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f

/-- Global coarse sections detected by their actual original coefficient restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:40"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
def openRow : Under R ⥤ WideSubcategory preservesZero.{u+1} :=
  InverseImageModelDiagram.diagram (openSourceTransformation f)

/-- The coarse global Model at an actual coefficient object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:44"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
def openModel (a : Under R) : WideSubcategory preservesZero.{u+1} := (openRow f).obj a

/-- The detected weak structure retains the original category, cofibrations and zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:47"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
def openWaldhausen (a : Under R) : Structure ((globalRow Q).obj a).obj.Obj :=
  Structure.withInverseImageWeak ((openSourceTransformation f).app a).hom.isExact

/-- Actual coarse restriction to the existing coefficient Model row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:51"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
def openRowRestriction : openRow f ⟶ boundedAboveFlatCoefficientOpenModelFunctor f :=
  InverseImageModelDiagram.restriction (openSourceTransformation f)

/-- The actual identity change from global fine to global coarse sections. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:55"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
def openRowChangeWeak : globalRow Q ⟶ openRow f :=
  InverseImageModelDiagram.changeWeak (openSourceTransformation f)

/-- Coarse restriction at a fixed coefficient object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:59"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
def openRestriction (a : Under R) : openModel f a ⟶ boundedAboveFlatCoefficientOpenModel f a :=
  (openRowRestriction f).app a

/-- The original global identity at a fixed coefficient object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:63"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
def openChangeWeak (a : Under R) : (globalRow Q).obj a ⟶ openModel f a :=
  (openRowChangeWeak f).app a

/-- The actual change-of-weakness restriction square commutes strictly. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:67"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
theorem openRowRestriction_changeWeak :
    openRowChangeWeak f ≫ openRowRestriction f =
      rowRestriction Q ≫ boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f :=
  InverseImageModelDiagram.factor (openSourceTransformation f)

/-- The component square retains both original zero-preserving arrows. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalOpenModels.lean:73"
  "adaptation" "Original coarse global section row detected by actual coefficient restriction"]
theorem openRestriction_changeWeak (a : Under R) :
    openChangeWeak f a ≫ openRestriction f a =
      (rowRestriction Q).app a ≫ boundedAboveFlatCoefficientOpenChangeWeakModelMap f a :=
  congrArg (fun η => η.app a) (openRowRestriction_changeWeak f)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
