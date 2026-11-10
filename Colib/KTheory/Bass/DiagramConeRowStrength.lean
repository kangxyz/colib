/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramRowRefinement
public import Colib.Topology.Prespectrum.RowRefinementPushout
public import Colib.Topology.Prespectrum.RowRefinementCone

/-!
# Forward row strength of the original strict-diagram cone

The actual pushout row strength commutes with the original constant comparison, and the
actual cone row strength then supplies a whole map from the cone of refined corners to the
refinement of the original cone. All four quotient generators retain the original heights.
No stable-equivalence assertion follows from this forward construction.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramConeRowStrength
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))

/-- The forward row strength on the original three-cell span. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:34-44"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def span (X : C) :
    StrictSquare.span ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X)) ⟶
      RowRefinement.spectrum (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X)))
        (DiagramRowInterchange.span Q F q hp hn X)
        (DiagramRowInterchange.span_point Q F q hp hn X) :=
  RowRefinement.pushoutStrength (F.map (Q.obj X).left.hom) (F.map (Q.obj X).hom.left)
    (q (Q.obj X).left.left) (q (Q.obj X).left.right) (q (Q.obj X).right.left)
    (hp (Q.obj X).left.left) (hp (Q.obj X).left.right) (hp (Q.obj X).right.left)
    (hn (Q.obj X).left.hom) (hn (Q.obj X).hom.left)

/-- The unchanged strict-square comparison acts on every row value. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:45-53"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def comparison (X : C) :
    RowRefinement.spectrum (StrictSquare.span (F.mapArrow.mapArrow.obj (Q.obj X)))
      (DiagramRowInterchange.span Q F q hp hn X)
      (DiagramRowInterchange.span_point Q F q hp hn X) ⟶
        (DiagramRowRefinement.diagram F q hp hn).obj (Q.obj X).right.right :=
  RowRefinement.map _ _ _ _ (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))
    (DiagramRowInterchange.comparison Q F q hp hn X)

/-- The actual span strength preserves both charts and the whole constant comparison overlap. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:54-72"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem span_comparison (X : C) :
    span Q F q hp hn X ≫ comparison Q F q hp hn X =
      StrictSquare.comparison ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj
        (Q.obj X)) := by
  apply HomotopyPushout.hom_ext
  · apply Hom.ext; funext n; apply ContinuousMap.ext; intro x
    cases n with
    | zero => apply Path.ext; funext r; apply Path.ext; funext s; rfl
    | succ k => apply Path.ext; funext s; rfl
  · apply Hom.ext; funext n; apply ContinuousMap.ext; intro x
    cases n with
    | zero => apply Path.ext; funext r; apply Path.ext; funext s; rfl
    | succ k => apply Path.ext; funext s; rfl
  · intro n t x
    cases n with
    | zero => apply Path.ext; funext r; apply Path.ext; funext s; rfl
    | succ k => apply Path.ext; funext s; rfl

/-- The original comparison arrow uses the span strength and unchanged final row corner. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:73-80"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def comparisonArrow (X : C) :
    Arrow.mk (StrictSquare.comparison
      ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X))) ⟶
      Arrow.mk (comparison Q F q hp hn X) :=
  Arrow.homMk (span Q F q hp hn X) (𝟙 _)
    ((span_comparison Q F q hp hn X).trans (Category.comp_id _).symm)

/-- The actual source is the unchanged cone construction on the row-refined diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:81-84"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
abbrev source (X : C) : LoopPrespectrum.{w} :=
  (ConeTrack.diagram Q (DiagramRowRefinement.diagram F q hp hn)).obj X

/-- The actual target is the computed row refinement of the original cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:85-89"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
abbrev target (X : C) : LoopPrespectrum.{w} :=
  RowRefinement.spectrum ((ConeTrack.diagram Q F).obj X)
    (DiagramRowInterchange.cone Q F q hp hn X) (DiagramRowInterchange.cone_point Q F q hp hn X)

/-- The original quotient map and whole cone null give the forward cone-row strength. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:90-97"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def strength (X : C) : source Q F q hp hn X ⟶ target Q F q hp hn X :=
  mappingConeMap (comparisonArrow Q F q hp hn X) ≫
    RowRefinement.coneStrength (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))
      (DiagramRowInterchange.span Q F q hp hn X) (q (Q.obj X).right.right)
      (DiagramRowInterchange.span_point Q F q hp hn X) (hp (Q.obj X).right.right)
      (DiagramRowInterchange.comparison Q F q hp hn X)

/-- Every original index arrow commutes with the full quotient strength, including degree zero. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:98-133"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_naturality {X Y : C} (g : X ⟶ Y) :
    (ConeTrack.diagram Q (DiagramRowRefinement.diagram F q hp hn)).map g ≫
        strength Q F q hp hn Y =
      strength Q F q hp hn X ≫
        RowRefinement.map (DiagramRowInterchange.cone Q F q hp hn X)
          (DiagramRowInterchange.cone Q F q hp hn Y)
          (DiagramRowInterchange.cone_point Q F q hp hn X)
          (DiagramRowInterchange.cone_point Q F q hp hn Y)
          ((ConeTrack.diagram Q F).map g)
          (DiagramRowInterchange.cone_naturality Q F q hp hn g) := by
  apply Hom.ext; funext n; apply ContinuousMap.ext; intro x
  cases n with
  | zero =>
    apply Path.ext; funext r; apply Path.ext; funext s
    induction x using Quot.inductionOn with
    | h z => cases z with
      | inl y => rfl
      | inr z =>
        rcases z with ⟨height, z⟩
        induction z using Quot.inductionOn with
        | h a => cases a with
          | inl a => cases a <;> rfl
          | inr a => rfl
  | succ k =>
    apply Path.ext; funext s
    induction x using Quot.inductionOn with
    | h z => cases z with
      | inl y => rfl
      | inr z =>
        rcases z with ⟨height, z⟩
        induction z using Quot.inductionOn with
        | h a => cases a with
          | inl a => cases a <;> rfl
          | inr a => rfl

/-- The original forward strength is an actual natural transformation of whole cone diagrams. -/
@[colib_tag "COL-0521", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:134-143"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def strengthNatTrans :
    ConeTrack.diagram Q (DiagramRowRefinement.diagram F q hp hn) ⟶
      DiagramRowRefinement.diagram (ConeTrack.diagram Q F)
        (DiagramRowInterchange.cone Q F q hp hn)
        (DiagramRowInterchange.cone_point Q F q hp hn)
        (DiagramRowInterchange.cone_naturality Q F q hp hn) where
  app := strength Q F q hp hn
  naturality _ _ := strength_naturality Q F q hp hn

/-- The actual original structure comparison commutes with the whole forward cone strength. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:144-180"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_comparison
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (X : C) :
    (ConeTrack.map Q (DiagramRowRefinement.comparison F q hp hn hs)).app X ≫
        strength Q F q hp hn X =
      RowRefinement.comparison ((ConeTrack.diagram Q F).obj X)
        (DiagramRowInterchange.cone Q F q hp hn X)
        (DiagramRowInterchange.cone_point Q F q hp hn X)
        (DiagramRowInterchange.cone_structure Q F q hp hn hs X) := by
  apply Hom.ext; funext n; apply ContinuousMap.ext; intro x
  cases n with
  | zero =>
    apply Path.ext; funext r; apply Path.ext; funext s
    induction x using Quot.inductionOn with
    | h z => cases z with
      | inl y => rfl
      | inr z =>
        rcases z with ⟨height, z⟩
        induction z using Quot.inductionOn with
        | h a => cases a with
          | inl a => cases a <;> rfl
          | inr a => rfl
  | succ k =>
    apply Path.ext; funext s
    induction x using Quot.inductionOn with
    | h z => cases z with
      | inl y => rfl
      | inr z =>
        rcases z with ⟨height, z⟩
        induction z using Quot.inductionOn with
        | h a => cases a with
          | inl a => cases a <;> rfl
          | inr a => rfl

/-- The full original source null retains its cone height and the independent row coordinate. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:181-191"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_sourceNull_succ (X : C) (k : ℕ) (t s : unitInterval)
    (γ : Path ((F.obj (Q.obj X).left.left).point (k + 2))
      ((F.obj (Q.obj X).left.left).point (k + 2))) :
    Path.toContinuousMap ((strength Q F q hp hn X).map (k + 1)
      ((StrictSquare.sourceNullHomotopy
        ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X))).level
          (k + 1) (t, γ))) s =
      (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level
        (k + 2) (t, γ s) := rfl

/-- The full original null at degree zero keeps both row times and the actual cone height. -/
@[colib_tag "COL-0521", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramConeRowStrength.lean:192-201"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem strength_sourceNull_zero (X : C) (t r s : unitInterval)
    (γ : Path (Path.refl ((F.obj (Q.obj X).left.left).point 2))
      (Path.refl ((F.obj (Q.obj X).left.left).point 2))) :
    Path.toContinuousMap (Path.toContinuousMap ((strength Q F q hp hn X).map 0
      ((StrictSquare.sourceNullHomotopy
        ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj (Q.obj X))).level
          0 (t, γ))) r) s =
      (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X))).level
        2 (t, γ r s) := rfl

end KTheory.Bass.DiagramConeRowStrength
