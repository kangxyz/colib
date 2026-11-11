/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.HomotopyWordNaturality
public import Colib.KTheory.Bass.DiagramSquareNull
public import Colib.KTheory.Bass.LoopStrength

/-! # Original coefficient-natural null/unit/null seed word

Only the original whole-word construction and its same-time naturality are selected.
No comparison under Bass, stability or telescope statement is assumed here.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.WholeSeedCospan
open PushoutCofiberSquare SquareConeStrength HomotopyWord
variable {C : Type u} [Category.{v} C]
variable (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))
  (A : ∀ X, Homotopy ((S.left.hom ≫ S.hom.right).app X)
    ((S.left.hom ≫ S.hom.right).app X)) (hA : Natural A)

/-- The supplied original unit track followed by the original cone inclusion. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/WholeSeedCospan.lean:53"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def coneAction (X : C) :
    Homotopy (((S.left.hom ≫ S.hom.right) ≫ coneInclusion (comparison S)).app X)
      (((S.left.hom ≫ S.hom.right) ≫ coneInclusion (comparison S)).app X) :=
  (A X).postcomp (mappingConeInclusion ((comparison S).app X))

include hA in
/-- The original cone-action track is coefficient-natural at identical time. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/WholeSeedCospan.lean:60"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
theorem coneAction_naturality : Natural (coneAction S A) :=
  natural_postcomp A hA (coneInclusion (comparison S))

/-- The exact original null/unit/null word, with its two original half clocks. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/WholeSeedCospan.lean:64"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def word (X : C) : Homotopy
    ((diagramZeroMap S.left.left (mappingConeDiagram (comparison S))).app X)
    ((diagramZeroMap S.left.left (mappingConeDiagram (comparison S))).app X) :=
  (sourceNull S X).symm.trans ((coneAction S A X).trans (sourceNull S X))

include hA in
/-- The exact original word is natural at every original time. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/WholeSeedCospan.lean:71"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
theorem word_naturality : Natural (word S A) :=
  natural_trans _ _ (natural_symm _ (sourceNull_naturality S))
    (natural_trans _ _ (coneAction_naturality S A hA) (sourceNull_naturality S))

/-- Its unchanged zero-loop map is the actual natural seed. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/WholeSeedCospan.lean:76"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def seed : S.left.left ⟶ mappingConeDiagram (comparison S) ⋙ parameterLoopingFunctor :=
  LoopStrength.loopMap (word S A) (word_naturality S A hA)

end KTheory.Bass.WholeSeedCospan

attribute [colib_tag "COL-0554"]
  KTheory.Bass.WholeSeedCospan.word

attribute [colib_tag "COL-0554"]
  KTheory.Bass.WholeSeedCospan.word_naturality

attribute [colib_tag "COL-0554"]
  KTheory.Bass.WholeSeedCospan.seed
