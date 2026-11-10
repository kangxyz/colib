/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowIteration
public import Colib.KTheory.Waldhausen.Iterated.RowHomotopyPushout

/-!
# Genuine row interchange at every original model Bass stage

Start with the actual last-row transposition of each Waldhausen realization and compute its
finite span/cone/parameter-loop images. Every arrow, point and two-structure equation is proved
from that original transposition. In particular the cone at Bass stage `i` is not treated as a
Model. These data support its actual row refinement; stability is a separate finite-range result.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass.ModelDiagramRowInterchange
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (F : C ⥤ WideSubcategory preservesZero.{w})

/-- The unchanged genuine quotient-row interchange at the initial Model diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:29"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
def initial (X : C) (k : ℕ) :
    C((prespectrum (F.obj X)).space (k + 3), (prespectrum (F.obj X)).space (k + 3)) :=
  RowHomotopyPushout.vertex k (F.obj X)

/-- Its point is the original Model basepoint. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:34"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem initial_point (X : C) (k : ℕ) :
    initial F X k ((prespectrum (F.obj X)).point (k + 3)) =
      (prespectrum (F.obj X)).point (k + 3) :=
  RowHomotopyPushout.vertex_point k (F.obj X)

/-- Actual exact Model maps preserve the original row transpose. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:40"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem initial_naturality {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : (prespectrum (F.obj X)).space (k + 3)) :
    initial F Y k ((prespectrumMap (F.map g)).map (k + 3) x) =
      (prespectrumMap (F.map g)).map (k + 3) (initial F X k x) :=
  RowHomotopyPushout.vertex_naturality k (F.map g) x

/-- The two original structure directions interchange at the genuine first stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:47"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem initial_structure (X : C) (k : ℕ) (x : (prespectrum (F.obj X)).space (k + 1))
    (s t : unitInterval) :
    initial F X k ((prespectrum (F.obj X)).structureMap (k + 2)
      ((prespectrum (F.obj X)).structureMap (k + 1) x s) t) =
        (prespectrum (F.obj X)).structureMap (k + 2)
          ((prespectrum (F.obj X)).structureMap (k + 1) x t) s :=
  stageLoopMap_rowSwap k (F.obj X) x s t

/-- Compute the actual row interchange at the original Bass stage `i`. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:56"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
def stage (i : ℕ) (X : C) (k : ℕ) :
    C((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (k + 3),
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (k + 3)) :=
  DiagramRowInterchange.iterate Q i (F ⋙ prespectrumFunctor)
    (initial F) (initial_point F) (initial_naturality F) X k

/-- Every finite stage fixes its own actual point. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:63"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem stage_point (i : ℕ) (X : C) (k : ℕ) :
    stage Q F i X k ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).point
      (k + 3)) =
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).point (k + 3) :=
  DiagramRowInterchange.iterate_point Q i _ _ _ _ X k

/-- Every original coefficient arrow is equivariant at every actual Bass stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:70"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem stage_naturality (i : ℕ) {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (k + 3)) :
    stage Q F i Y k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).map g).map (k + 3) x) =
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).map g).map (k + 3)
        (stage Q F i X k x) :=
  DiagramRowInterchange.iterate_naturality Q i _ _ _ _ g k x

/-- The genuine double-structure equation holds at every finite Bass stage. -/
@[colib_tag "COL-0529", colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:79"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem stage_structure (i : ℕ) (X : C) (k : ℕ)
    (x : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space (k + 1))
    (s t : unitInterval) :
    stage Q F i X k
      ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap (k + 2)
        ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap (k + 1)
          x s) t) =
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap (k + 2)
        ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).structureMap (k + 1)
          x t) s :=
  DiagramRowInterchange.iterate_structure Q i _ _ _ _ (initial_structure F) X k x s t

/-- The original next unlooped cone carries the explicitly computed finite row interchange. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:92"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
def cone (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w}) (X : C) (k : ℕ) :
    C(((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X).space
        (k + 3),
      ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X).space
        (k + 3)) :=
  DiagramRowInterchange.cone Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))
    (stage Q F i) (stage_point Q F i) (stage_naturality Q F i) X k

/-- Each actual finite cone fixes the same original quotient point. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:101"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem cone_point (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w}) (X : C) (k : ℕ) :
    cone Q i F X k
      (((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X).point
        (k + 3)) =
      ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor))).obj X).point
        (k + 3) :=
  DiagramRowInterchange.cone_point Q _ _ _ _ X k

/-- Every coefficient arrow preserves the actual cone at every original Bass stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:110"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem cone_naturality (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w})
    {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
      (F ⋙ prespectrumFunctor))).obj X).space (k + 3)) :
    cone Q i F Y k
      (((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor))).map g).map (k + 3) x) =
      ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor))).map g).map (k + 3) (cone Q i F X k x) :=
  DiagramRowInterchange.cone_naturality Q _ _ _ _ g k x

/-- The actual cone at every stage satisfies the required two-structure interchange. -/
@[colib_tag "COL-0529", colib_ref "quillen"
  "Quillen/KTheory/Bass/ModelDiagramRowInterchange.lean:121"
  "adaptation" "Original row and unit constructions on native zero-preserving exact objects."]
theorem cone_structure (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w}) (X : C) (k : ℕ)
    (x : ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
      (F ⋙ prespectrumFunctor))).obj X).space (k + 1)) (s t : unitInterval) :
    cone Q i F X k
      (((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor))).obj X).structureMap (k + 2)
          (((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
            (F ⋙ prespectrumFunctor))).obj X).structureMap (k + 1) x s) t) =
      ((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor))).obj X).structureMap (k + 2)
          (((ConeTrack.diagram Q ((strictDiagramIterate Q i).obj
            (F ⋙ prespectrumFunctor))).obj X).structureMap (k + 1) x t) s :=
  DiagramRowInterchange.cone_structure Q _ _ _ _ (stage_structure Q F i) X k x s t

end KTheory.Bass.ModelDiagramRowInterchange
