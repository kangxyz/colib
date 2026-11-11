/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowRefinement
public import Colib.Topology.Prespectrum.RowRefinementHomotopy

/-!
# Actual target-arrow and whole-homotopy action on row diagrams

An original transformation acts on row-refined diagrams when it preserves the actual row
interchange. A prescribed natural whole homotopy then acts on every row with its original
time, assuming its full row square rather than only its endpoint squares.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowRefinement
variable {C : Type u} [Category.{v} C] {F G : C ⥤ LoopPrespectrum.{w}}
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

/-- Each original target transformation acts pointwise on the whole refined diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowRefinementHomotopy.lean:38-62"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def map : diagram F qF pF nF ⟶ diagram G qG pG nG where
  app X := RowRefinement.map (qF X) (qG X) (pF X) (pG X) (η.app X) (hη X)
  naturality {X Y} g := by
    apply Hom.ext; funext n; apply ContinuousMap.ext; intro γ
    cases n with
    | zero =>
      change Path (Path.refl ((F.obj X).point 2)) (Path.refl ((F.obj X).point 2)) at γ
      apply Path.ext; funext r; apply Path.ext; funext s
      exact congrArg (fun a => a.map 2 (γ r s)) (η.naturality g)
    | succ k =>
      change Path ((F.obj X).point (k + 2)) ((F.obj X).point (k + 2)) at γ
      apply Path.ext; funext s
      exact congrArg (fun a => a.map (k + 2) (γ s)) (η.naturality g)

variable (θ : F ⟶ G)
  (hθ : ∀ X k x, qG X k ((θ.app X).map (k + 3) x) =
    (θ.app X).map (k + 3) (qF X k x))
  (H : ∀ X, Homotopy (η.app X) (θ.app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) n t x,
    (G.map g).map n ((H X).level n (t, x)) =
      (H Y).level n (t, (F.map g).map n x))
  (hrow : ∀ X k t x, qG X k ((H X).level (k + 3) (t, x)) =
    (H X).level (k + 3) (t, qF X k x))

/-- The prescribed whole homotopy acts at exactly the original time on each actual row. -/
@[colib_tag "COL-0519", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowRefinementHomotopy.lean:63-69"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
def homotopy (X : C) :
    Homotopy ((map qF pF nF qG pG nG η hη).app X)
      ((map qF pF nF qG pG nG θ hθ).app X) :=
  RowRefinement.homotopy (qF X) (qG X) (pF X) (pG X) (hη X) (hθ X) (H X) (hrow X)

include hH in
/-- Whole homotopy naturality holds at the unchanged time and at every row coordinate. -/
@[colib_tag "COL-0519", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowRefinementHomotopy.lean:70-85"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem homotopy_naturality {X Y : C} (g : X ⟶ Y) (n : ℕ) (t : unitInterval)
    (γ : ((diagram F qF pF nF).obj X).space n) :
    ((diagram G qG pG nG).map g).map n
        ((homotopy qF pF nF qG pG nG η hη θ hθ H hrow X).level n (t, γ)) =
      (homotopy qF pF nF qG pG nG η hη θ hθ H hrow Y).level n
        (t, ((diagram F qF pF nF).map g).map n γ) := by
  cases n with
  | zero =>
    change Path (Path.refl ((F.obj X).point 2)) (Path.refl ((F.obj X).point 2)) at γ
    apply Path.ext; funext r; apply Path.ext; funext s
    exact hH g 2 t (γ r s)
  | succ k =>
    change Path ((F.obj X).point (k + 2)) ((F.obj X).point (k + 2)) at γ
    apply Path.ext; funext s
    exact hH g (k + 2) t (γ s)

end KTheory.Bass.DiagramRowRefinement
