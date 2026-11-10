/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramConeRowStrength
public import Colib.KTheory.Bass.DiagramRowRefinementHomotopy

/-!
# Whole target-homotopy naturality of the actual cone-row strength

The forward strength preserves every time slice of a specified row-natural diagram homotopy.
The equality is checked on the target, both span charts and the entire overlap, with their
original quotient heights. Unit time and all row coordinates remain independent, including
the explicit degree-zero double row.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramConeRowStrength
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) {F G : C ⥤ LoopPrespectrum.{w}}
  (qF : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (pF : ∀ X k, qF X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (nF : ∀ {X Y} (g : X ⟶ Y) k x,
    qF Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (qF X k x))
  (qG : ∀ X k, C((G.obj X).space (k + 3), (G.obj X).space (k + 3)))
  (pG : ∀ X k, qG X k ((G.obj X).point (k + 3)) = (G.obj X).point (k + 3))
  (nG : ∀ {X Y} (g : X ⟶ Y) k x,
    qG Y k ((G.map g).map (k + 3) x) = (G.map g).map (k + 3) (qG X k x))
  (η : F ⟶ G)
  (hη : ∀ X k x, qG X k ((η.app X).map (k + 3) x) =
    (η.app X).map (k + 3) (qF X k x))
  (θ : F ⟶ G)
  (hθ : ∀ X k x, qG X k ((θ.app X).map (k + 3) x) =
    (θ.app X).map (k + 3) (qF X k x))
  (H : ∀ X, Homotopy (η.app X) (θ.app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) n t x,
    (G.map g).map n ((H X).level n (t, x)) =
      (H Y).level n (t, (F.map g).map n x))
  (hrow : ∀ X k t x, qG X k ((H X).level (k + 3) (t, x)) =
    (H X).level (k + 3) (t, qF X k x))

/-- The actual original cone construction on the complete pointwise row homotopy. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrengthHomotopy.lean:49-58"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def rowConeHomotopy (X : C) :
    Homotopy
      ((ConeTrack.map Q (DiagramRowRefinement.map qF pF nF qG pG nG η hη)).app X)
      ((ConeTrack.map Q (DiagramRowRefinement.map qF pF nF qG pG nG θ hθ)).app X) :=
  (diagramSquareMapHomotopy
    (DiagramRowRefinement.homotopy qF pF nF qG pG nG η hη θ hθ H hrow)
    (DiagramRowRefinement.homotopy_naturality qF pF nF qG pG nG η hη θ hθ H hH hrow)
    (Q.obj X)).cone

/-- Positive whole-time naturality retains unit, row, cone and overlap coordinates separately. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrengthHomotopy.lean:59-76"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_homotopy_succ (X : C) (k : ℕ) (t s : unitInterval)
    (x : (source Q F qF pF nF X).space (k + 1)) :
    Path.toContinuousMap ((strength Q G qG pG nG X).map (k + 1)
      ((rowConeHomotopy Q qF pF nF qG pG nG η hη θ hθ H hH hrow X).level (k + 1)
        (t, x))) s =
      (diagramSquareMapHomotopy H hH (Q.obj X)).cone.level (k + 2)
        (t, Path.toContinuousMap ((strength Q F qF pF nF X).map (k + 1) x) s) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y => rfl
    | inr z =>
      rcases z with ⟨height, z⟩
      induction z using Quot.inductionOn with
      | h a => cases a with
        | inl a => cases a <;> rfl
        | inr a => rfl

/-- Degree-zero whole-time naturality retains both row coordinates and all original heights. -/
@[colib_tag "COL-0521", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrengthHomotopy.lean:77-94"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_homotopy_zero (X : C) (t r s : unitInterval)
    (x : (source Q F qF pF nF X).space 0) :
    Path.toContinuousMap (Path.toContinuousMap ((strength Q G qG pG nG X).map 0
      ((rowConeHomotopy Q qF pF nF qG pG nG η hη θ hθ H hH hrow X).level 0
        (t, x))) r) s =
      (diagramSquareMapHomotopy H hH (Q.obj X)).cone.level 2
        (t, Path.toContinuousMap (Path.toContinuousMap
          ((strength Q F qF pF nF X).map 0 x) r) s) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y => rfl
    | inr z =>
      rcases z with ⟨height, z⟩
      induction z using Quot.inductionOn with
      | h a => cases a with
        | inl a => cases a <;> rfl
        | inr a => rfl

end KTheory.Bass.DiagramConeRowStrength
