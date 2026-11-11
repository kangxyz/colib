/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ForwardPushoutStrength
public import Colib.KTheory.Bass.CofiberComparisonInclusion
public import Colib.KTheory.Bass.DiagramSquareNull
public import Colib.Topology.Prespectrum.StrictSquareNull

/-!
# Forward cone strength of a strict natural square

The actual Bass pushout comparison commutes with the original strict-square
comparison on both chart inclusions and the whole constant overlap track.
Its original cone map followed by the forward cofiber comparison preserves
all time slices of the original source-leg null. No variable interchange or
additional coherence hypothesis is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.SquareConeStrength
open PushoutStrength PushoutCofiberSquare
variable {C : Type u} [Category.{v} C]

/-- The original comparison retains its left chart. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:42"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem left_comparison (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))) :
    left S.left.hom S.hom.left ≫ comparison S = S.hom.right := by
  apply NatTrans.ext
  funext X
  apply Hom.ext; funext n; ext x; rfl

/-- The original comparison retains its right chart. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:49"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem right_comparison (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))) :
    right S.left.hom S.hom.left ≫ comparison S = S.right.hom := by
  apply NatTrans.ext
  funext X
  apply Hom.ext; funext n; ext x; rfl

/-- Every original overlap slice descends to the same constant strict-square composite. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:56"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem glueAt_comparison (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))
    (r : unitInterval) :
    diagramHomotopyAt (glue S.left.hom S.hom.left)
      (glue_naturality S.left.hom S.hom.left) r ≫ comparison S =
        S.left.hom ≫ S.hom.right := by
  apply NatTrans.ext
  funext X
  apply Hom.ext; funext n; ext x; rfl

variable (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))
  (Q : C ⥤ Arrow (Arrow C))

/-- Apply the existing Bass functor to all four original corners and arrows. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:69"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
def bassSquare : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})) :=
  (strictDiagramFunctor Q).mapArrow.mapArrow.obj S

/-- The original pushout strength and strict-square comparison commute at every generator. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:73"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem rho_comparison :
    rho S.left.hom S.hom.left Q ≫ (strictDiagramFunctor Q).map (comparison S) =
      comparison (bassSquare S Q) := by
  apply NatTrans.ext
  funext X
  apply HomotopyPushout.hom_ext
  · apply Hom.ext
    funext n
    ext x
    exact congrArg (fun a => (a.app X).map n x)
      (((strictDiagramFunctor Q).map_comp (left S.left.hom S.hom.left)
        (comparison S)).symm.trans
        (congrArg (fun a => (strictDiagramFunctor Q).map a) (left_comparison S)))
  · apply Hom.ext
    funext n
    ext x
    exact congrArg (fun a => (a.app X).map n x)
      (((strictDiagramFunctor Q).map_comp (right S.left.hom S.hom.left)
        (comparison S)).symm.trans
        (congrArg (fun a => (strictDiagramFunctor Q).map a) (right_comparison S)))
  · intro n r x
    change (((strictDiagramFunctor Q).map (comparison S)).app X).map n
      ((strictDiagramMapHomotopy (glue S.left.hom S.hom.left)
        (glue_naturality S.left.hom S.hom.left) Q X).at r |>.map n x) =
      ((((strictDiagramFunctor Q).map S.left.hom).app X) ≫
        (((strictDiagramFunctor Q).map S.hom.right).app X)).map n x
    rw [strictDiagramMapHomotopy_at]
    exact congrArg (fun a => (a.app X).map n x)
      ((((strictDiagramFunctor Q).map_comp
        (diagramHomotopyAt (glue S.left.hom S.hom.left)
          (glue_naturality S.left.hom S.hom.left) r) (comparison S)).symm.trans
        (congrArg (fun a => (strictDiagramFunctor Q).map a) (glueAt_comparison S r))).trans
        ((strictDiagramFunctor Q).map_comp S.left.hom S.hom.right))

/-- The actual square uses rho on the span and the identity at the final corner. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:108"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
def comparisonArrow :
    Arrow.mk (comparison (bassSquare S Q)) ⟶
      Arrow.mk ((strictDiagramFunctor Q).map (comparison S)) :=
  Arrow.homMk (rho S.left.hom S.hom.left Q) (𝟙 _)
    ((rho_comparison S Q).trans (Category.comp_id _).symm)

/-- Original cone descent followed by the forward cofiber comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:115"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
def chi : mappingConeDiagram (comparison (bassSquare S Q)) ⟶
    (strictDiagramFunctor Q).obj (mappingConeDiagram (comparison S)) :=
  Functor.whiskerRight (ArrowDiagrams.toDiagram.map (comparisonArrow S Q))
    mappingConeFunctor ≫ strictDiagramCofiberComparison Q (comparison S)

/-- The comparison retains the actual original cone inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:121"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem chi_inclusion (X : C) :
    mappingConeInclusion ((comparison (bassSquare S Q)).app X) ≫ (chi S Q).app X =
      (((strictDiagramFunctor Q).map (coneInclusion (comparison S))).app X) := by
  change mappingConeInclusion (((strictDiagramFunctor Q).map (comparison S)).app X) ≫
      (strictDiagramCofiberComparison Q (comparison S)).app X = _
  exact cofiberComparison_inclusion (comparison S) Q X

/-- Every original outer cone time is retained before the positive cofiber comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:129"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem chi_cylinder (X : C) (n : ℕ) (r : unitInterval)
    (x : ((pushout (bassSquare S Q).left.hom (bassSquare S Q).hom.left).obj X).space n) :
    ((chi S Q).app X).map n
      ((mappingConeHomotopy ((comparison (bassSquare S Q)).app X)).level n (r, x)) =
    (((strictDiagramFunctor Q).map
      (diagramHomotopyAt (coneNull (comparison S))
        (coneNull_naturality (comparison S)) r)).app X).map n
          ((rho S.left.hom S.hom.left Q).app X |>.map n x) := by
  exact cofiberComparison_cylinder (comparison S) Q X n r
    ((rho S.left.hom S.hom.left Q).app X |>.map n x)

/-- The literal left source leg of the original strict square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:141"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
def sourceLeg : S.left.left ⟶ pushout S.left.hom S.hom.left :=
  S.left.hom ≫ left S.left.hom S.hom.left

/-- Rho preserves the original source leg, not a replacement null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:145"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem sourceLeg_rho :
    sourceLeg (bassSquare S Q) ≫ rho S.left.hom S.hom.left Q =
      (strictDiagramFunctor Q).map (sourceLeg S) := by
  apply NatTrans.ext
  funext X
  apply Hom.ext
  funext n
  ext x
  exact congrArg (fun a => (a.app X).map n x)
    ((strictDiagramFunctor Q).map_comp S.left.hom (left S.left.hom S.hom.left)).symm

/-- Its original slice is the original cone contraction restricted to the left source leg. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:169"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem sourceNullAt (r : unitInterval) :
    sourceLeg S ≫ diagramHomotopyAt (coneNull (comparison S))
      (coneNull_naturality (comparison S)) r =
    diagramHomotopyAt (sourceNull S) (sourceNull_naturality S) r := by
  apply NatTrans.ext
  funext X
  apply Hom.ext; funext n; ext x; rfl

/-- Chi preserves every original source-null time, including the independent output loop. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SquareConeStrength.lean:178"
  "adaptation" "Original forward square-cone strength preserving the whole source null."]
theorem chi_sourceNull (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj S.left.left).obj X).space n) :
    ((chi S Q).app X).map n ((sourceNull (bassSquare S Q) X).level n (r, x)) =
      (strictDiagramMapHomotopy (sourceNull S) (sourceNull_naturality S) Q X).level n (r, x) := by
  change ((chi S Q).app X).map n
    ((mappingConeHomotopy ((comparison (bassSquare S Q)).app X)).level n
      (r, ((sourceLeg (bassSquare S Q)).app X).map n x)) = _
  rw [chi_cylinder]
  change (((sourceLeg (bassSquare S Q) ≫ rho S.left.hom S.hom.left Q) ≫
    (strictDiagramFunctor Q).map (diagramHomotopyAt (coneNull (comparison S))
      (coneNull_naturality (comparison S)) r)).app X).map n x =
      ((strictDiagramMapHomotopy (sourceNull S) (sourceNull_naturality S) Q X).at r).map n x
  rw [sourceLeg_rho, ← CategoryTheory.Functor.map_comp, sourceNullAt,
    strictDiagramMapHomotopy_at]
  rfl

end KTheory.Bass.SquareConeStrength
