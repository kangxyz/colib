/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0ChartSharedNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0MergeIndex

/-!
# The common 62-simplex for the supported H₀ and Bass boundary faces

All 31 H₀ nodes and all 45 old boundary nodes retain their entire dependent
reference data. The two orders need not be globally monotone; restriction to
a supported face requires its own monotonicity witness. Adapted from
`BassH0MergedNodes.lean` and `BassH0MergedFaces.lean` in Quillen,
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

/-- Relabel an actually supported old face in its proved monotone order. -/
def oldFace {k : ℕ} (α : ⦋k⦌ ⟶ ⦋44⦌)
    (h : Monotone (oldIndex ∘ α.toOrderHom)) : ⦋k⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨oldIndex ∘ α.toOrderHom, h⟩

/-- Relabel an actually supported H0 face in its proved monotone order. -/
def h0Face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (h0Index ∘ α.toOrderHom)) : ⦋k⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨h0Index ∘ α.toOrderHom, h⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The representatives use the actual old and H0 nodes, including their original references. -/
def nodes (i : Fin 63) : BoundedFlatCoefficientBassOverlap.Node P u v :=
  Sum.elim (BoundedFlatCoefficientBassReferenceMerge.nodes P u v)
    (BoundedFlatCoefficientBassH0Merge.nodes P u v) (select i)

/-- Every original old node retains its full dependent data in the new order. -/
theorem old_nodes (i : Fin 45) : nodes P u v (oldIndex i) =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v i := by
  unfold nodes
  rw [select_old]
  rfl

/-- All H0 nodes retain their full dependent data, using the thirteen proved actual identities. -/
theorem h0_nodes (i : Fin 31) : nodes P u v (h0Index i) =
    BoundedFlatCoefficientBassH0Merge.nodes P u v i := by
  unfold nodes
  rw [select_h0]
  fin_cases i
  · rfl
  · rfl
  · exact (BoundedFlatCoefficientBassH0Merge.shared_source_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_positive_bottom_raw_node P u v).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (BoundedFlatCoefficientBassH0Merge.shared_positive_center_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_positive_laurent_raw_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_positive_target_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_positive_polynomial_raw_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_positive_polynomial_target_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_negative_bottom_raw_node P u v).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (BoundedFlatCoefficientBassH0Merge.shared_negative_center_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_negative_laurent_raw_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_negative_target_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_negative_polynomial_raw_node P u v).symm
  · exact (BoundedFlatCoefficientBassH0Merge.shared_negative_polynomial_target_node P u v).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The actual 62-simplex uses only the original full nodes and their canonical common reference. -/
def simplex : ModelSimplex
    (asSmallCategory (W (space (op P, a))))
    (asSmallCategory (W
      (space (op P, (laurentUnderFunctor R).obj c)))) 62 :=
  ModelSimplex.ofIsos (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

/-- Any supported old face is retained with every original full reference node. -/
theorem old_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋44⦌)
    (h : Monotone (oldIndex ∘ α.toOrderHom)) :
    (simplex P u v).face (oldFace α h) =
      (BoundedFlatCoefficientBassReferenceMerge.simplex P u v).face α := by
  unfold simplex BoundedFlatCoefficientBassReferenceMerge.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  apply ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ nodes P u v ((oldFace α h).toOrderHom i))
    (fun i ↦ BoundedFlatCoefficientBassReferenceMerge.nodes P u v (α.toOrderHom i))
  intro i
  exact old_nodes P u v (α.toOrderHom i)

/-- Any supported H0 face is retained with its actual canonically transported references. -/
theorem h0_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (h0Index ∘ α.toOrderHom)) :
    (simplex P u v).face (h0Face α h) =
      (BoundedFlatCoefficientBassH0Merge.simplex P u v).face α := by
  unfold simplex BoundedFlatCoefficientBassH0Merge.simplex ModelSimplex.reanchorSimplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  apply ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ nodes P u v ((h0Face α h).toOrderHom i))
    (fun i ↦ BoundedFlatCoefficientBassH0Merge.nodes P u v (α.toOrderHom i))
  intro i
  exact h0_nodes P u v (α.toOrderHom i)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged
