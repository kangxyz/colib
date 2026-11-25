/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareSharedNodes

/-! The three native double-square triples with their actual shared nodes identified. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareMergedSimplex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Representatives ordered so that all three original eight-vertex diagrams remain faces. -/
def select : Fin 18 → Fin 24 := ![0, 1, 2, 3, 9, 10, 11, 19, 4, 5, 6, 7, 14, 15, 20, 21, 22, 23]

/-- The 18 selected common-diagram nodes, retaining their functors and source reference
isomorphisms. -/
def nodes (i : Fin 18) : BoundedFlatPerfectDoubleSquareCommonSimplex.Node p q c :=
  BoundedFlatPerfectDoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq (select i)

/-- The actual 17-simplex uses the original nodes and proven common reference equations. -/
def simplex : ModelSimplex (asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn A))
    (asSmallCategory (BoundedFlatPerfectTripleSimplex.structureOn C')) 17 :=
  ModelSimplex.ofIsos (BoundedFlatPerfectTripleSimplex.source c q p)
    (fun i ↦ (nodes p q p' q' a b c hp hq i).1)
    (fun i ↦ (nodes p q p' q' a b c hp hq i).2)

/-- The face inclusion retaining the first split-triple diagram in the merged 17-simplex. -/
def firstFace : ⦋7⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 3, 8, 9, 10, 11], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The face inclusion retaining the middle split-triple diagram in the merged 17-simplex. -/
def middleFace : ⦋7⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 4, 5, 6, 8, 9, 12, 13], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The face inclusion retaining the last split-triple diagram in the merged 17-simplex. -/
def lastFace : ⦋7⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 4, 5, 7, 14, 15, 16, 17], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

theorem first_nodes (i : Fin 8) : nodes p q p' q' a b c hp hq (firstFace.toOrderHom i) =
    BoundedFlatPerfectDoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareCommonSimplex.firstFace.toOrderHom i) := by
  unfold nodes
  apply congrArg (BoundedFlatPerfectDoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq)
  fin_cases i <;> rfl

theorem middle_nodes (i : Fin 8) : nodes p q p' q' a b c hp hq (middleFace.toOrderHom i) =
    BoundedFlatPerfectDoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareCommonSimplex.middleFace.toOrderHom i) := by
  fin_cases i
  · exact BoundedFlatPerfectDoubleSquareCommonSimplex.source_middle_shared p q p' q' a b c hp hq
  · rfl
  · rfl
  · rfl
  · exact BoundedFlatPerfectDoubleSquareCommonSimplex.right_raw_shared p q p' q' a b c hp hq
  · exact BoundedFlatPerfectDoubleSquareCommonSimplex.right_normalized_shared p q p' q' a b c hp hq
  · rfl
  · rfl

theorem last_nodes (i : Fin 8) : nodes p q p' q' a b c hp hq (lastFace.toOrderHom i) =
    BoundedFlatPerfectDoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq
      (BoundedFlatPerfectDoubleSquareCommonSimplex.lastFace.toOrderHom i) := by
  fin_cases i
  · exact BoundedFlatPerfectDoubleSquareCommonSimplex.source_last_shared p q p' q' a b c hp hq
  · exact BoundedFlatPerfectDoubleSquareCommonSimplex.left_raw_shared p q p' q' a b c hp hq
  · exact BoundedFlatPerfectDoubleSquareCommonSimplex.left_normalized_shared p q p' q' a b c hp hq
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The whole first old split triple is retained after identifying the shared nodes. -/
theorem first_face : (simplex p q p' q' a b c hp hq).face firstFace =
    BoundedFlatPerfectSplitTripleSimplex.simplex c q p := by
  rw [← BoundedFlatPerfectDoubleSquareCommonSimplex.first_face p q p' q' a b c hp hq]
  unfold simplex BoundedFlatPerfectDoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (first_nodes p q p' q' a b c hp hq)

/-- The middle old split triple shares its actual first intermediate with the first face. -/
theorem middle_face : (simplex p q p' q' a b c hp hq).face middleFace =
    BoundedFlatPerfectSplitTripleSimplex.simplex q' b p := by
  rw [← BoundedFlatPerfectDoubleSquareCommonSimplex.middle_face p q p' q' a b c hp hq]
  unfold simplex BoundedFlatPerfectDoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (middle_nodes p q p' q' a b c hp hq)

/-- The last old split triple shares the actual middle total with the middle face. -/
theorem last_face : (simplex p q p' q' a b c hp hq).face lastFace =
    BoundedFlatPerfectSplitTripleSimplex.simplex q' p' a := by
  rw [← BoundedFlatPerfectDoubleSquareCommonSimplex.last_face p q p' q' a b c hp hq]
  unfold simplex BoundedFlatPerfectDoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (last_nodes p q p' q' a b c hp hq)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareMergedSimplex
