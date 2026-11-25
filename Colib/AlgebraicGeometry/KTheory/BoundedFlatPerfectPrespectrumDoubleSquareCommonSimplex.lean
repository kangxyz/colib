/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleSimplex
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceSimplex

/-! One genuine common-reference diagram for the three native double-square triples.
Repeated slots are retained: this statement alone does not identify shared scalar boundaries.

Adapted from Quillen's `BoundedFlat/DoubleSquareCommonSimplex.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareCommonSimplex
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "source" => BoundedFlatPerfectTripleSimplex.source
open BoundedFlatPerfectSplitTripleSimplex (vertices references)

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

include hq in
/-- The inner commuting square identifies the two triple composites. -/
theorem middle_eq : q' ≫ b ≫ p = c ≫ q ≫ p := by
  rw [← Category.assoc, ← hq, Category.assoc]

include hp hq in
/-- The two original square equations identify the outer triple composite. -/
theorem total_eq : (q' ≫ p') ≫ a = c ≫ q ≫ p := by
  rw [Category.assoc, ← hp]
  exact middle_eq p q q' b c hq

/-- The actual first square transports the middle triple's reference functor. -/
def middleSourceIso : (source c q p).hom.toFunctor ≅
    (source q' b p).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      (middle_eq p q q' b c hq).symm)) AsSmall.up)

/-- Both actual square equations, with the displayed scheme association,
transport the last source. -/
def lastSourceIso : (source c q p).hom.toFunctor ≅
    (source q' p' a).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback
      ((total_eq p q p' q' a b c hp hq).symm.trans
        (Category.assoc q' p' a)))) AsSmall.up)

/-- An existing exact functor equipped with its reference from the actual total source. -/
abbrev Node := Σ F : asSmallCategory (W A) ⟶
    asSmallCategory (W C'),
      (source c q p).hom.toFunctor ≅ F.hom.toFunctor

/-- Each slot stores an actual existing exact functor and its displayed source isomorphism. -/
def nodes : Fin 24 → Node p q c := fun i ↦
  Fin.addCases (m := 8) (n := 16) (motive := fun _ ↦ Node p q c)
    (fun j ↦ ⟨vertices c q p j, references c q p j⟩)
    (fun j ↦ Fin.addCases (m := 8) (n := 8) (motive := fun _ ↦ Node p q c)
      (fun k ↦ ⟨vertices q' b p k,
        middleSourceIso p q q' b c hq ≪≫ references q' b p k⟩)
      (fun k ↦ ⟨vertices q' p' a k,
        lastSourceIso p q p' q' a b c hp hq ≪≫ references q' p' a k⟩) j) i

theorem first_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (Fin.castAdd 16 i) =
      ⟨vertices c q p i, references c q p i⟩ := by
  unfold nodes
  rw [Fin.addCases_left]

theorem middle_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 i)) =
      ⟨vertices q' b p i,
        middleSourceIso p q q' b c hq ≪≫ references q' b p i⟩ := by
  unfold nodes
  rw [Fin.addCases_right, Fin.addCases_left]

theorem last_nodes (i : Fin 8) :
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.natAdd 8 i)) =
      ⟨vertices q' p' a i,
        lastSourceIso p q p' q' a b c hp hq ≪≫ references q' p' a i⟩ := by
  unfold nodes
  rw [Fin.addCases_right, Fin.addCases_right]

/-- A common 23-simplex contains all three eight-slot native comparison diagrams. -/
def simplex : ModelSimplex (asSmallCategory (W A))
    (asSmallCategory (W C')) 23 :=
  ModelSimplex.ofIsos (source c q p)
    (fun i ↦ (nodes p q p' q' a b c hp hq i).1)
    (fun i ↦ (nodes p q p' q' a b c hp hq i).2)

/-- The face inclusion selecting vertices 0 through 7 for the first split-triple diagram. -/
def firstFace : ⦋7⦌ ⟶ ⦋23⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.castAdd 16, fun _ _ h ↦ h⟩

/-- The face inclusion selecting vertices 8 through 15 for the middle split-triple diagram. -/
def middleFace : ⦋7⦌ ⟶ ⦋23⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ Fin.natAdd 8 (Fin.castAdd 8 i), by
    intro i j hij
    exact Nat.add_le_add_left hij 8⟩

/-- The face inclusion selecting vertices 16 through 23 for the last split-triple diagram. -/
def lastFace : ⦋7⦌ ⟶ ⦋23⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ Fin.natAdd 8 (Fin.natAdd 8 i), by
    intro i j hij
    exact Nat.add_le_add_left (Nat.add_le_add_left hij 8) 8⟩

/-- The whole first original split-triple diagram is the displayed common face. -/
theorem first_face :
    (BoundedFlatPerfectDoubleSquareCommonSimplex.simplex p q p' q' a b c hp hq).face
      firstFace =
    BoundedFlatPerfectSplitTripleSimplex.simplex c q p := by
  unfold BoundedFlatPerfectDoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _
    (fun i ↦ ⟨vertices c q p i, references c q p i⟩)
    (first_nodes p q p' q' a b c hp hq)

/-- The whole middle diagram retains the first actual square equality in its reference. -/
theorem middle_face :
    (BoundedFlatPerfectDoubleSquareCommonSimplex.simplex p q p' q' a b c hp hq).face
      middleFace =
    BoundedFlatPerfectSplitTripleSimplex.simplex q' b p := by
  unfold BoundedFlatPerfectDoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _
    (fun i ↦ ⟨vertices q' b p i,
      middleSourceIso p q q' b c hq ≪≫ references q' b p i⟩)
    (middle_nodes p q p' q' a b c hp hq)).trans
      (ModelSimplex.ofIsos_change_reference (middleSourceIso p q q' b c hq) _ _)

/-- The whole last diagram retains both square equalities and the original association. -/
theorem last_face :
    (BoundedFlatPerfectDoubleSquareCommonSimplex.simplex p q p' q' a b c hp hq).face
      lastFace =
    BoundedFlatPerfectSplitTripleSimplex.simplex q' p' a := by
  unfold BoundedFlatPerfectDoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _
    (fun i ↦ ⟨vertices q' p' a i,
      lastSourceIso p q p' q' a b c hp hq ≪≫ references q' p' a i⟩)
    (last_nodes p q p' q' a b c hp hq)).trans
      (ModelSimplex.ofIsos_change_reference (lastSourceIso p q p' q' a b c hp hq) _ _)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareCommonSimplex
