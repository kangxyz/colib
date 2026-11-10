/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.DiagramConeRowStrengthHomotopy
public import Colib.KTheory.Bass.StrictDiagramHomotopy
public import Colib.KTheory.Bass.LoopConeTrack

/-! # Independent cone descent of a natural cell into a genuine row refinement

The input is a whole cross-diagram cell, not a Model structure on the later spectrum.
Its four actual corners descend through the original square cone, inverse geometric index,
and forward row strength. The source-null height remains independent of the cell time.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowCell
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)

/-- Both endpoints of the independent cell use the actual coefficient followed by the row map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellCone.lean:37-48"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def input : F ⟶ L ⋙ DiagramRowRefinement.diagram F q hp hn :=
  Functor.whiskerRight c F ≫
    Functor.whiskerLeft L (DiagramRowRefinement.comparison F q hp hn hs)

variable
  (H : ∀ X, Homotopy ((input L c F q hp hn hs).app X)
    ((input L c F q hp hn hs).app X))
  (hH : ∀ {X Y} (g : X ⟶ Y) (n : ℕ) (t : unitInterval) (x : (F.obj X).space n),
    ((DiagramRowRefinement.diagram F q hp hn).map (L.map g)).map n
      ((H X).level n (t, x)) = (H Y).level n (t, (F.map g).map n x))

/-- The original four-corner moving square uses the independently given whole cell. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellCone.lean:49-55"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def square (S : Arrow (Arrow C)) :=
  diagramSquareMapHomotopy (η := input L c F q hp hn hs)
    (θ := input L c F q hp hn hs) H hH S

variable (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)

/-- Actual quotient descent precedes index transport and forward row strength. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellCone.lean:56-61"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
def cone (X : C) :=
  ((square L c F q hp hn hs H hH (Q.obj X)).cone).postcomp
    ((ConeTrack.indexMap Q L χ (DiagramRowRefinement.diagram F q hp hn)).app X ≫
      DiagramConeRowStrength.strength Q F q hp hn (L.obj X))

/-- The original source-null time survives the independent moving-square descent. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellCone.lean:62-71"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
theorem square_sourceNull (S : Arrow (Arrow C)) (n : ℕ) (r s : unitInterval)
    (x : (F.obj S.left.left).space n) :
    (square L c F q hp hn hs H hH S).cone.level n
        (r, (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj S)).level n (s, x)) =
      (StrictSquare.sourceNullHomotopy
        ((L ⋙ DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj S)).level n
          (s, (H S.left.left).level n (r, x)) :=
  (square L c F q hp hn hs H hH S).sourceNull_apply n r s x

/-- The complete original source null is retained after the actual index and row maps. -/
@[colib_tag "COL-0525", colib_ref "quillen"
  "Quillen/KTheory/Bass/DiagramRowCellCone.lean:72-90"
  "adaptation" "Original whole row-cell descent with independent time and computed successor"]
theorem cone_sourceNull (X : C) (n : ℕ) (r s : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space n) :
    (cone L c F q hp hn hs H hH Q χ X).level n
        (r, (StrictSquare.sourceNullHomotopy
          (F.mapArrow.mapArrow.obj (Q.obj X))).level n (s, x)) =
      (DiagramConeRowStrength.strength Q F q hp hn (L.obj X)).map n
        ((StrictSquare.sourceNullHomotopy
          ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.obj
            (Q.obj (L.obj X)))).level n
          (s, ((DiagramRowRefinement.diagram F q hp hn).map (χ.inv.app X).left.left).map n
            ((H (Q.obj X).left.left).level n (r, x)))) := by
  have h := square_sourceNull L c F q hp hn hs H hH (Q.obj X) n r s x
  have hm := congrArg (fun z =>
    ((ConeTrack.indexMap Q L χ (DiagramRowRefinement.diagram F q hp hn)).app X).map n z) h
  have hi := hm.trans (StrictSquare.sourceNullHomotopy_naturality_apply
    ((DiagramRowRefinement.diagram F q hp hn).mapArrow.mapArrow.map (χ.inv.app X)) n s
      ((H (Q.obj X).left.left).level n (r, x)))
  exact congrArg (fun z => (DiagramConeRowStrength.strength Q F q hp hn (L.obj X)).map n z) hi

end KTheory.Bass.DiagramRowCell
