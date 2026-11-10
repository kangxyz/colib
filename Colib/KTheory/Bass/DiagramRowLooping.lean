/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowInterchange
public import Colib.Topology.Prespectrum.RowInterchangeParameterLooping

/-!
# The actual Bass step preserves natural row interchange

Apply the original cone construction and then pointwise parameter looping. The resulting
row interchange has the same row index and retains the independent old loop, overlap height,
cone height and structure coordinates. All hypotheses concern the original diagram only.
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

/-- Pointwise looping of the computed original cone interchange is the Bass-step interchange. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowLooping.lean:32-37"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
def bass (X : C) (k : ℕ) :
    C((((strictDiagramFunctor Q).obj F).obj X).space (k + 3),
      (((strictDiagramFunctor Q).obj F).obj X).space (k + 3)) :=
  RowInterchange.parameterLoop (cone Q F q hp hn X) (cone_point Q F q hp hn X) k

/-- The Bass-step point remains the actual constant loop at the original quotient-cone point. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowLooping.lean:38-43"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem bass_point (X : C) (k : ℕ) :
    bass Q F q hp hn X k ((((strictDiagramFunctor Q).obj F).obj X).point (k + 3)) =
      (((strictDiagramFunctor Q).obj F).obj X).point (k + 3) :=
  RowInterchange.parameterLoop_point _ _ _

/-- Every original coefficient arrow commutes with the Bass-step interchange. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowLooping.lean:44-51"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem bass_naturality {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : (((strictDiagramFunctor Q).obj F).obj X).space (k + 3)) :
    bass Q F q hp hn Y k ((((strictDiagramFunctor Q).obj F).map g).map (k + 3) x) =
      (((strictDiagramFunctor Q).obj F).map g).map (k + 3) (bass Q F q hp hn X k x) :=
  RowInterchange.parameterLoop_map _ _ _ _ ((ConeTrack.diagram Q F).map g)
    (cone_naturality Q F q hp hn g) k x

/-- The original two structure times still interchange, without changing the old loop time. -/
@[colib_tag "COL-0517", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowLooping.lean:52-64"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem bass_structure
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (X : C) (k : ℕ) (x : (((strictDiagramFunctor Q).obj F).obj X).space (k + 1))
    (s t : unitInterval) :
    bass Q F q hp hn X k ((((strictDiagramFunctor Q).obj F).obj X).structureMap (k + 2)
      ((((strictDiagramFunctor Q).obj F).obj X).structureMap (k + 1) x s) t) =
        (((strictDiagramFunctor Q).obj F).obj X).structureMap (k + 2)
          ((((strictDiagramFunctor Q).obj F).obj X).structureMap (k + 1) x t) s :=
  RowInterchange.parameterLoop_structure _ _ (cone_structure Q F q hp hn hs X) k x s t

end KTheory.Bass.DiagramRowInterchange
