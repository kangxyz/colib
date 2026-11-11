/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowLooping

/-!
# Explicit finite iteration of the original natural row interchange

The recursion computes each finite interchange by the original cone and parameter-looping
formulas. A subtype stores only the already proved point and ordinary arrow equations needed
to apply the next quotient construction. No interchange or compatibility is chosen, and no
all-stage property is assumed. The two-structure equation is proved separately by induction.
The index `i` is the Bass stage; `k` remains the independent iterated-S level.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowInterchange
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

/-- Compute the finite quotient/loop interchange, storing its proved local point and arrow laws.
-/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowIteration.lean:29-52"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
def iterateData (i : ℕ) (F : C ⥤ LoopPrespectrum.{w})
    (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
    (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
    (hn : ∀ {X Y} (g : X ⟶ Y) k x,
      q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x)) :
    { qi : ∀ X k, C((((strictDiagramIterate Q i).obj F).obj X).space (k + 3),
        (((strictDiagramIterate Q i).obj F).obj X).space (k + 3)) //
      (∀ X k, qi X k ((((strictDiagramIterate Q i).obj F).obj X).point (k + 3)) =
        (((strictDiagramIterate Q i).obj F).obj X).point (k + 3)) ∧
      (∀ {X Y} (g : X ⟶ Y) k x,
        qi Y k ((((strictDiagramIterate Q i).obj F).map g).map (k + 3) x) =
          (((strictDiagramIterate Q i).obj F).map g).map (k + 3) (qi X k x)) } :=
  match i with
  | 0 => ⟨q, hp, hn⟩
  | i + 1 => iterateData i ((strictDiagramFunctor Q).obj F)
      (bass Q F q hp hn) (bass_point Q F q hp hn) (bass_naturality Q F q hp hn)

variable (i : ℕ) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))

/-- The actual computed interchange at each independent Bass stage and spectrum level. -/
@[colib_tag "COL-0517", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowIteration.lean:53-58"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
def iterate (X : C) (k : ℕ) :
    C((((strictDiagramIterate Q i).obj F).obj X).space (k + 3),
      (((strictDiagramIterate Q i).obj F).obj X).space (k + 3)) :=
  (iterateData Q i F q hp hn).val X k

/-- Every finite stage fixes its original point. -/
@[colib_tag "COL-0517", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowIteration.lean:59-64"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem iterate_point (X : C) (k : ℕ) :
    iterate Q i F q hp hn X k ((((strictDiagramIterate Q i).obj F).obj X).point (k + 3)) =
      (((strictDiagramIterate Q i).obj F).obj X).point (k + 3) :=
  (iterateData Q i F q hp hn).property.1 X k

/-- Ordinary diagram naturality is proved at every finite stage. -/
@[colib_tag "COL-0517", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowIteration.lean:65-71"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem iterate_naturality {X Y : C} (g : X ⟶ Y) (k : ℕ)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space (k + 3)) :
    iterate Q i F q hp hn Y k ((((strictDiagramIterate Q i).obj F).map g).map (k + 3) x) =
      (((strictDiagramIterate Q i).obj F).map g).map (k + 3) (iterate Q i F q hp hn X k x) :=
  (iterateData Q i F q hp hn).property.2 g k x

/-- The actual two-structure equation propagates through every finite cone and old loop. -/
@[colib_tag "COL-0517", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowIteration.lean:72-89"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem iterate_structure
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (X : C) (k : ℕ) (x : (((strictDiagramIterate Q i).obj F).obj X).space (k + 1))
    (s t : unitInterval) :
    iterate Q i F q hp hn X k ((((strictDiagramIterate Q i).obj F).obj X).structureMap (k + 2)
      ((((strictDiagramIterate Q i).obj F).obj X).structureMap (k + 1) x s) t) =
        (((strictDiagramIterate Q i).obj F).obj X).structureMap (k + 2)
          ((((strictDiagramIterate Q i).obj F).obj X).structureMap (k + 1) x t) s := by
  induction i generalizing F with
  | zero => exact hs X k x s t
  | succ i ih =>
    exact ih ((strictDiagramFunctor Q).obj F) (bass Q F q hp hn)
      (bass_point Q F q hp hn) (bass_naturality Q F q hp hn)
      (bass_structure Q F q hp hn hs) x

end KTheory.Bass.DiagramRowInterchange
