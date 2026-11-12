/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.DiagramRowNormalizedBoundary
public import Colib.KTheory.Bass.DiagramRowNormalizedBoundaryHomotopy
public import Colib.KTheory.Bass.DiagramRowInputNaturality
public import Colib.Topology.Prespectrum.RowNormalizationNaturality

/-!
# Naturality of the original normalized boundary prism

An equivariant transformation and preservation of the independent corner cell preserve the
whole normalized boundary homotopy. The specified source null is retained through the actual
cone and row comparison; its square is proved rather than assumed.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowSeed
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  {F G : C ⥤ LoopPrespectrum.{w}}
  (qF : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hpF : ∀ X k, qF X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hnF : ∀ {X Y} (g : X ⟶ Y) k x,
    qF Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (qF X k x))
  (qG : ∀ X k, C((G.obj X).space (k + 3), (G.obj X).space (k + 3)))
  (hpG : ∀ X k, qG X k ((G.obj X).point (k + 3)) = (G.obj X).point (k + 3))
  (hnG : ∀ {X Y} (g : X ⟶ Y) k x,
    qG Y k ((G.map g).map (k + 3) x) = (G.map g).map (k + 3) (qG X k x))
  (hsF : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    qF X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
  (hsG : ∀ X k (x : (G.obj X).space (k + 1)) (s t : unitInterval),
    qG X k ((G.obj X).structureMap (k + 2) ((G.obj X).structureMap (k + 1) x s) t) =
      (G.obj X).structureMap (k + 2) ((G.obj X).structureMap (k + 1) x t) s)
  (η : F ⟶ G)
  (hη : ∀ X k x, qG X k ((η.app X).map (k + 3) x) =
    (η.app X).map (k + 3) (qF X k x))


/-- The actual row map on the original cones of an equivariant transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNormalizedBoundaryNaturality.lean:49"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
abbrev coneRowMap (X : C) : carrier Q F qF hpF hnF X ⟶ carrier Q G qG hpG hnG X :=
  RowRefinement.map _ _ _ _ ((ConeTrack.map Q η).app X)
    (DiagramRowInterchange.cone_input_naturality Q qF hpF hnF qG hpG hnG η hη X)

/-- The actual last-corner row map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNormalizedBoundaryNaturality.lean:54"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
abbrev cornerRowMap (X : C) :=
  RowRefinement.map (qF (Q.obj X).right.right) (qG (Q.obj X).right.right)
    (hpF (Q.obj X).right.right) (hpG (Q.obj X).right.right)
    (η.app (Q.obj X).right.right) (hη (Q.obj X).right.right)

/-- Cone inclusion commutes with the actual row maps, including degree zero. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNormalizedBoundaryNaturality.lean:60"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem inclusion_input_naturality (X : C) :
    inclusion Q F qF hpF hnF X ≫ coneRowMap Q qF hpF hnF qG hpG hnG η hη X =
      cornerRowMap Q qF hpF qG hpG η hη X ≫ inclusion Q G qG hpG hnG X := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero =>
    apply Path.ext
    funext r
    apply Path.ext
    funext s
    rfl
  | succ k =>
    apply Path.ext
    funext s
    rfl

/-- The unchanged original source null is natural after the actual row comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNormalizedBoundaryNaturality.lean:80"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem includedNull_naturality_apply (X : C) (n : ℕ) (t : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space n) :
    (coneRowMap Q qF hpF hnF qG hpG hnG η hη X).map n
      ((includedNull Q F qF hpF hnF hsF X).level n (t, x)) =
    (includedNull Q G qG hpG hnG hsG X).level n
      (t, (η.app (Q.obj X).left.left).map n x) := by
  have hc := RowRefinement.comparison_naturality
    (DiagramRowInterchange.cone Q F qF hpF hnF X)
    (DiagramRowInterchange.cone Q G qG hpG hnG X)
    (DiagramRowInterchange.cone_point Q F qF hpF hnF X)
    (DiagramRowInterchange.cone_point Q G qG hpG hnG X)
    ((ConeTrack.map Q η).app X)
    (DiagramRowInterchange.cone_input_naturality Q qF hpF hnF qG hpG hnG η hη X)
    (DiagramRowInterchange.cone_structure Q F qF hpF hnF hsF X)
    (DiagramRowInterchange.cone_structure Q G qG hpG hnG hsG X)
  have hn := StrictSquare.sourceNullHomotopy_naturality_apply
    (diagramSquareMap η (Q.obj X)) n t x
  exact (congrArg (fun f => f.map n
    ((StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level n
      (t, x))) hc).symm.trans
    (congrArg (fun y => (comparison Q G qG hpG hnG hsG X).map n y) hn)

/-- The included endpoint square follows from the actual original null at its source. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNormalizedBoundaryNaturality.lean:103"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem includedEndpoint_naturality (X : C) :
    ((diagonal Q F X ≫ cornerComparison Q F qF hpF hsF X) ≫
      inclusion Q F qF hpF hnF X) ≫ coneRowMap Q qF hpF hnF qG hpG hnG η hη X =
    η.app (Q.obj X).left.left ≫
      ((diagonal Q G X ≫ cornerComparison Q G qG hpG hsG X) ≫
        inclusion Q G qG hpG hnG X) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  have h := includedNull_naturality_apply Q qF hpF hnF qG hpG hnG hsF hsG η hη X n 0 x
  rw [(includedNull Q F qF hpF hnF hsF X).at_zero,
    (includedNull Q G qG hpG hnG hsG X).at_zero] at h
  exact h

variable (X : C)
  (KF : Homotopy (diagonal Q F X ≫ cornerComparison Q F qF hpF hsF X)
    (diagonal Q F X ≫ cornerComparison Q F qF hpF hsF X))
  (KG : Homotopy (diagonal Q G X ≫ cornerComparison Q G qG hpG hsG X)
    (diagonal Q G X ≫ cornerComparison Q G qG hpG hsG X))
  (hK : ∀ n t x, (cornerRowMap Q qF hpF qG hpG η hη X).map n
    (KF.level n (t, x)) = KG.level n (t, (η.app (Q.obj X).left.left).map n x))

include hK

/-- Only the original independent cell square is needed after inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNormalizedBoundaryNaturality.lean:129"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem includedCell_naturality_apply (n : ℕ) (t : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space n) :
    (coneRowMap Q qF hpF hnF qG hpG hnG η hη X).map n
      ((KF.postcomp (inclusion Q F qF hpF hnF X)).level n (t, x)) =
    (KG.postcomp (inclusion Q G qG hpG hnG X)).level n
      (t, (η.app (Q.obj X).left.left).map n x) :=
  (congrArg (fun f => f.map n (KF.level n (t, x)))
    (inclusion_input_naturality Q qF hpF hnF qG hpG hnG η hη X)).trans
      (congrArg (fun y => (inclusion Q G qG hpG hnG X).map n y) (hK n t x))

/-- Normalized boundaries commute with an equivariant original diagram transformation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNormalizedBoundaryNaturality.lean:140"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedBoundary_naturality :
    normalizedBoundary Q F qF hpF hnF hsF X KF ≫
      parameterLoopingMap (coneRowMap Q qF hpF hnF qG hpG hnG η hη X) =
    η.app (Q.obj X).left.left ≫ normalizedBoundary Q G qG hpG hnG hsG X KG := by
  rw [normalizedBoundary_eq, normalizedBoundary_eq]
  exact RowRefinement.normalizedOperation_square _ _ _ _ _ _ _ _ _ _ _
    (includedEndpoint_naturality Q qF hpF hnF qG hpG hnG hsF hsG η hη X)
    (includedCell_naturality_apply Q qF hpF hnF qG hpG hnG hsF hsG η hη X KF KG hK)

/-- The complete normalized boundary prism is natural, with every time left independent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowNormalizedBoundaryNaturality.lean:150"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedBoundaryHomotopy_naturality_apply (n : ℕ) (s : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space n) :
    (parameterLoopingMap (coneRowMap Q qF hpF hnF qG hpG hnG η hη X)).map n
      ((normalizedBoundaryHomotopy Q F qF hpF hnF hsF X KF).level n (s, x)) =
    (normalizedBoundaryHomotopy Q G qG hpG hnG hsG X KG).level n
      (s, (η.app (Q.obj X).left.left).map n x) := by
  exact congrArg (fun f => f (s, x))
    (RowRefinement.normalizationHomotopy_square_level _ _ _ _ _ _ _ _ _ _ _
      (includedEndpoint_naturality Q qF hpF hnF qG hpG hnG hsF hsG η hη X)
      (includedCell_naturality_apply Q qF hpF hnF qG hpG hnG hsF hsG η hη X KF KG hK)
      (includedNull Q F qF hpF hnF hsF X) (includedNull Q G qG hpG hnG hsG X)
      (includedNull_naturality_apply Q qF hpF hnF qG hpG hnG hsF hsG η hη X) n)

end KTheory.Bass.DiagramRowSeed
