/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.StrictSquarePushout

/-!
# Two original total cones of a strict square of squares

An actual four-dimensional strict arrow diagram supplies a pointwise pushout
square and its original constant comparison to the final square. The checked
square-cone/pushout isomorphism intertwines this comparison on all twelve raw
strata. Taking the original cone and applying the existing cone/square
interchange gives the second totalization. Its target is the actual
`coneSquare` of that comparison, rather than an implicitly identified transpose.
No geometric product swap or higher coherence is supplied as a hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare

/-- The original unlooped total-cone functor of a strict square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareCone.lean:31"
  "adaptation" "Original actual double totalization and complete comparison square."]
def totalFunctor : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u} :=
  strictSquareComparisonFunctor ⋙ mappingConeFunctor

namespace Double
variable (E : Arrow (Arrow (Arrow (Arrow LoopPrespectrum.{u}))))

/-- Compare the outer square at one actual functorial inner coordinate. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareCone.lean:38"
  "adaptation" "Original actual double totalization and complete comparison square."]
def cornerComparison (K : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u}) :
    HomotopyPushout.prespectrum (K.map E.left.hom) (K.map E.hom.left) ⟶ K.obj E.right.right :=
  comparison (K.mapArrow.mapArrow.obj E)

/-- A natural coordinate map retains the original constant comparison at every overlap time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareCone.lean:43"
  "adaptation" "Original actual double totalization and complete comparison square."]
theorem cornerComparison_naturality
    {K L : Arrow (Arrow LoopPrespectrum.{u}) ⥤ LoopPrespectrum.{u}} (e : K ⟶ L) :
    HomotopyPushout.map (K.map E.left.hom) (K.map E.hom.left)
        (L.map E.left.hom) (L.map E.hom.left)
        (e.app E.left.left) (e.app E.left.right) (e.app E.right.left)
        (e.naturality E.left.hom) (e.naturality E.hom.left) ≫ cornerComparison E L =
      cornerComparison E K ≫ e.app E.right.right :=
  by
    let a : K.mapArrow.mapArrow.obj E ⟶ L.mapArrow.mapArrow.obj E :=
      ((Functor.mapArrowFunctor (Arrow (Arrow (Arrow LoopPrespectrum.{u})))
        (Arrow LoopPrespectrum.{u})).map
          ((Functor.mapArrowFunctor (Arrow (Arrow LoopPrespectrum.{u}))
            LoopPrespectrum.{u}).map e)).app E
    exact comparison_naturality a

/-- The actual pointwise comparison from the original pushout square to the final square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareCone.lean:59"
  "adaptation" "Original actual double totalization and complete comparison square."]
def comparisonMap : Pushout.square E.left.hom E.hom.left ⟶ E.right.right :=
  Arrow.homMk
    (Arrow.homMk (cornerComparison E (Arrow.leftFunc ⋙ Arrow.leftFunc))
      (cornerComparison E (Arrow.leftFunc ⋙ Arrow.rightFunc))
      (cornerComparison_naturality E
        (Functor.whiskerLeft Arrow.leftFunc Arrow.leftToRight)).symm)
    (Arrow.homMk (cornerComparison E (Arrow.rightFunc ⋙ Arrow.leftFunc))
      (cornerComparison E (Arrow.rightFunc ⋙ Arrow.rightFunc))
      (cornerComparison_naturality E
        (Functor.whiskerLeft Arrow.rightFunc Arrow.leftToRight)).symm)
    (by
      apply Arrow.hom_ext
      · exact (cornerComparison_naturality E
          (Functor.whiskerRight Arrow.leftToRight Arrow.leftFunc)).symm
      · exact (cornerComparison_naturality E
          (Functor.whiskerRight Arrow.leftToRight Arrow.rightFunc)).symm)

/-- The actual source isomorphism retains the full original outer comparison. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareCone.lean:77"
  "adaptation" "Original actual double totalization and complete comparison square."]
theorem sourceIso_comparison :
    (Pushout.totalIso E.left.hom E.hom.left).hom ≫ totalFunctor.map (comparisonMap E) =
      comparison (totalFunctor.mapArrow.mapArrow.obj E) := by
  apply HomotopyPushout.hom_ext
  · apply mappingCone_hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · intro n r q
      induction q using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z <;> rfl
        | inr z => rfl
  · apply mappingCone_hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · intro n r q
      induction q using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z <;> rfl
        | inr z => rfl
  · intro n s q
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => rfl
      | inr z =>
        rcases z with ⟨r,q⟩
        induction q using Quot.inductionOn with
        | h z => cases z with
          | inl z => cases z <;> rfl
          | inr z => rfl

/-- The two original outer comparison arrows are isomorphic with identity target. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareCone.lean:107"
  "adaptation" "Original actual double totalization and complete comparison square."]
def comparisonArrowIso :
    Arrow.mk (comparison (totalFunctor.mapArrow.mapArrow.obj E)) ≅
      Arrow.mk (totalFunctor.map (comparisonMap E)) :=
  Arrow.isoMk
    (f := Arrow.mk (comparison (totalFunctor.mapArrow.mapArrow.obj E)))
    (g := Arrow.mk (totalFunctor.map (comparisonMap E)))
    (Pushout.totalIso E.left.hom E.hom.left) (Iso.refl _)
    ((sourceIso_comparison E).trans (Category.comp_id _).symm)

/-- The original two-totalization interchange with its actual pointwise-cone target. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictDoubleSquareCone.lean:117"
  "adaptation" "Original actual double totalization and complete comparison square."]
def interchangeIso : totalFunctor.obj (totalFunctor.mapArrow.mapArrow.obj E) ≅
    totalFunctor.obj (coneSquare (comparisonMap E)) :=
  mappingConeFunctor.mapIso (comparisonArrowIso E) ≪≫ coneInterchangeIso (comparisonMap E)

end Double
end Topology.LoopPrespectrum.StrictSquare
