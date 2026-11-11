/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageDiagram

/-! # The actual relative-open global Model diagram detected by geometric restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

/-- The original global Model on the open scheme of every pair. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:22"
  "adaptation" "Original strict diagram; only detected weak classes change."]
def pairOpenAmbient : Scheme.OpenPairs.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u+1} :=
  (MorphismProperty.Arrow.forget (@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊤ ⊤ ⋙
    Arrow.leftFunc).op ⋙ boundedAboveFlatGlobalSectionModelFunctor

/-- Original scheme restriction is strict on the full open-pair category. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:26"
  "adaptation" "Original strict diagram; only detected weak classes change."]
def pairRestriction : pairAmbient.{u} ⟶ pairOpenAmbient where
  app A := boundedAboveFlatGlobalSectionModelFunctor.map A.unop.hom.op
  naturality A B g := by
    change boundedAboveFlatGlobalSectionModelFunctor.map g.unop.right.op ≫
      boundedAboveFlatGlobalSectionModelFunctor.map B.unop.hom.op =
      boundedAboveFlatGlobalSectionModelFunctor.map A.unop.hom.op ≫
        boundedAboveFlatGlobalSectionModelFunctor.map g.unop.left.op
    rw [← boundedAboveFlatGlobalSectionModelFunctor.map_comp,
      ← boundedAboveFlatGlobalSectionModelFunctor.map_comp]
    exact congrArg boundedAboveFlatGlobalSectionModelFunctor.map
      (congrArg Quiver.Hom.op (Arrow.w g.unop.hom)).symm

/-- Keep the ambient category, cofibrations and original zero, detecting weakness on the open. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:35"
  "adaptation" "Original strict diagram; only detected weak classes change."]
def pairOpen : Scheme.OpenPairs.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u+1} :=
  InverseImageDiagram.diagram pairRestriction

/-- The identity on original global sections changes only the weak class. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:39"
  "adaptation" "Original strict diagram; only detected weak classes change."]
def pairChangeWeak : pairAmbient.{u} ⟶ pairOpen :=
  InverseImageDiagram.changeWeak pairRestriction

/-- The original geometric restriction is exact for these detected open weak equivalences. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:43"
  "adaptation" "Original strict diagram; only detected weak classes change."]
def pairOpenRestriction : pairOpen.{u} ⟶ pairOpenAmbient :=
  InverseImageDiagram.restriction pairRestriction

/-- The relative-open factorization is the same original global scheme map. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:47"
  "adaptation" "Original strict diagram; only detected weak classes change."]
theorem pairOpen_factor : pairChangeWeak.{u} ≫ pairOpenRestriction = pairRestriction :=
  InverseImageDiagram.factor pairRestriction

namespace ParameterModels
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The relative-open Model on each actual integer-base product pair. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:54"
  "adaptation" "Original strict diagram; only detected weak classes change."]
def openModel : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u+1} :=
  (GlobalSupportedParameter.pairs f).op ⋙ pairOpen

/-- Change only the original weak class in every parameter. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:58"
  "adaptation" "Original strict diagram; only detected weak classes change."]
def changeWeak : ambient Q ⟶ openModel f :=
  Functor.whiskerLeft (GlobalSupportedParameter.pairs f).op pairChangeWeak

/-- Restrict the actual relative-open global sections to the genuine open product. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalOpenPairDiagram.lean:62"
  "adaptation" "Original strict diagram; only detected weak classes change."]
def openRestriction : openModel f ⟶ ambient P :=
  Functor.whiskerLeft (GlobalSupportedParameter.pairs f).op pairOpenRestriction

end ParameterModels
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection

attribute [colib_tag "COL-0539"] pairOpen
attribute [colib_tag "COL-0539"] pairOpen_factor

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
