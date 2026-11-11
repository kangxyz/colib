/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.ConeTrack
public import Colib.Topology.Prespectrum.RowInterchangeHomotopyPushout
public import Colib.Topology.Prespectrum.RowInterchangeMappingCone

/-!
# Natural row interchanges on the original strict diagram cone

The actual natural interchanges of a prespectrum diagram descend through its prescribed
strict square, reduced span, constant comparison, and quotient cone. All comparison and
source-null equations are proved from the original arrow squares. The two-structure equation
is retained separately from naturality; no Omega-spectrum or Model assumption is imposed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowInterchange
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))

/-- The original span carries its three actual corner interchanges. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:34-42"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
def span (X : C) (k : ℕ) :
    C((StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).space (k + 3),
      (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).space (k + 3)) :=
  RowInterchange.pushout (F.map (Q.obj X).left.hom) (F.map (Q.obj X).hom.left)
    (q (Q.obj X).left.left) (q (Q.obj X).left.right) (q (Q.obj X).right.left)
    (hp (Q.obj X).left.left) (hp (Q.obj X).left.right)
    (hn (Q.obj X).left.hom) (hn (Q.obj X).hom.left) k

/-- The same reduced span point is fixed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:43-48"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem span_point (X : C) (k : ℕ) :
    span Q F q hp hn X k ((StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).point
      (k + 3)) = (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).point (k + 3) :=
  RowInterchange.pushout_point _ _ _ _ _ _ _ _ _ _

/-- The complete original constant comparison is equivariant, including its entire overlap. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:49-62"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem comparison (X : C) (k : ℕ)
    (x : (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).space (k + 3)) :
    q (Q.obj X).right.right k
      ((StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))).map (k + 3) x) =
    (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))).map (k + 3)
      (span Q F q hp hn X k x) := by
  apply RowInterchange.pushout_desc
  · exact hn (Q.obj X).hom.right
  · exact hn (Q.obj X).right.hom
  · intro j t y
    exact (hn (Q.obj X).hom.right j ((F.map (Q.obj X).left.hom).map (j + 3) y)).trans
      (congrArg ((F.map (Q.obj X).hom.right).map (j + 3)) (hn (Q.obj X).left.hom j y))

/-- The prescribed quotient cone carries its original span and final-corner interchanges. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:63-70"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
def cone (X : C) (k : ℕ) :
    C(((ConeTrack.diagram Q F).obj X).space (k + 3),
      ((ConeTrack.diagram Q F).obj X).space (k + 3)) :=
  RowInterchange.cone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))
    (span Q F q hp hn X) (q (Q.obj X).right.right)
    (span_point Q F q hp hn X) (hp (Q.obj X).right.right) (comparison Q F q hp hn X) k

/-- The original cone point is fixed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:71-76"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_point (X : C) (k : ℕ) :
    cone Q F q hp hn X k (((ConeTrack.diagram Q F).obj X).point (k + 3)) =
      ((ConeTrack.diagram Q F).obj X).point (k + 3) :=
  RowInterchange.cone_point _ _ _ _ _ _ _

/-- Every original diagram arrow preserves all three span cells at the same overlap height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:77-96"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem span_naturality {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).space (k + 3)) :
    span Q F q hp hn Y k
      ((StrictSquare.spanMap (F.mapArrow.mapArrow.map (Q.map g))).map (k + 3) x) =
    (StrictSquare.spanMap (F.mapArrow.mapArrow.map (Q.map g))).map (k + 3)
      (span Q F q hp hn X k x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y =>
        exact congrArg (HomotopyPushout.left (F.map (Q.obj Y).left.hom)
          (F.map (Q.obj Y).hom.left) (k + 3)) (hn (Q.map g).left.right k y)
      | inr y =>
        exact congrArg (HomotopyPushout.right (F.map (Q.obj Y).left.hom)
          (F.map (Q.obj Y).hom.left) (k + 3)) (hn (Q.map g).right.left k y)
    | inr z =>
      exact congrArg (fun y => HomotopyPushout.cylinder (F.map (Q.obj Y).left.hom)
        (F.map (Q.obj Y).hom.left) (k + 3) (z.1, y)) (hn (Q.map g).left.left k z.2)

/-- The actual cone diagram is row-natural, using the original strict comparison-map square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:97-105"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_naturality {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : ((ConeTrack.diagram Q F).obj X).space (k + 3)) :
    cone Q F q hp hn Y k (((ConeTrack.diagram Q F).map g).map (k + 3) x) =
      ((ConeTrack.diagram Q F).map g).map (k + 3) (cone Q F q hp hn X k x) := by
  apply RowInterchange.cone_map
  · exact span_naturality Q F q hp hn g
  · exact hn (Q.map g).right.right

/-- The original positive source null retains its exact height and source-leg value. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:106-124"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem sourceNull (X : C) (k : ℕ) (t : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space (k + 3)) :
    cone Q F q hp hn X k
      ((StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level (k + 3)
        (t, x)) =
      (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level (k + 3)
        (t, q (Q.obj X).left.left k x) := by
  exact congrArg (fun y => (mappingConeHomotopy
    (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))).level (k + 3)
      (t, HomotopyPushout.left (F.map (Q.obj X).left.hom)
        (F.map (Q.obj X).hom.left) (k + 3) y)) (hn (Q.obj X).left.hom k x)

variable (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
  q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
    (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)

include hs

/-- The actual double-structure equation descends through all three original span cells. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:125-136"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem span_structure (X : C) (k : ℕ)
    (x : (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).space (k + 1))
    (s t : unitInterval) :
    span Q F q hp hn X k
      ((StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).structureMap (k + 2)
        ((StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).structureMap (k + 1) x s) t) =
      (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).structureMap (k + 2)
        ((StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X))).structureMap (k + 1) x t) s :=
  RowInterchange.pushout_structure _ _ _ _ _ _ _ _ _
    (hs (Q.obj X).left.left) (hs (Q.obj X).left.right) (hs (Q.obj X).right.left) k x s t

/-- The original two structure times interchange on the entire finite cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowInterchange.lean:137-146"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_structure (X : C) (k : ℕ) (x : ((ConeTrack.diagram Q F).obj X).space (k + 1))
    (s t : unitInterval) :
    cone Q F q hp hn X k (((ConeTrack.diagram Q F).obj X).structureMap (k + 2)
      (((ConeTrack.diagram Q F).obj X).structureMap (k + 1) x s) t) =
        ((ConeTrack.diagram Q F).obj X).structureMap (k + 2)
          (((ConeTrack.diagram Q F).obj X).structureMap (k + 1) x t) s :=
  RowInterchange.cone_structure _ _ _ _ _ _ (span_structure Q F q hp hn hs X)
    (hs (Q.obj X).right.right) k x s t

end KTheory.Bass.DiagramRowInterchange
