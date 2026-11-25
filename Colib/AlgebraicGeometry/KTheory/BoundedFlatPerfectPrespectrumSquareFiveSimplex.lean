/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBinarySimplex
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceSimplex

/-!
# The exact five-node family of a commuting pullback square

The common-source binary normalization triangles retain both original raw intermediates.
Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/NativeSquareFiveSimplex.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectNativeSquareFiveSimplex
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w)

/-- The binary normalization source for the route `p ≫ v` through the commuting square. -/
abbrev source := BoundedFlatPerfectBinarySimplex.sourceMap p v

include h in
/-- The actual square equality identifies the two original binary source functors. -/
theorem source_eq :
    (source p v).hom.toFunctor = (BoundedFlatPerfectBinarySimplex.sourceMap q w).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback h)

/--
The isomorphism from the `p, v` binary source to the `q, w` binary source induced by the square
equality `h`.
-/
def sourceIso := eqToIso (source_eq p v q w h)

/-- A model morphism equipped with a natural isomorphism from the fixed `p, v` source functor. -/
abbrev Node := Σ F : asSmallCategory (W Z) ⟶
    asSmallCategory (W X), (source p v).hom.toFunctor ≅ F.hom.toFunctor

/-- Both actual raw normalization intermediates are retained separately. -/
def nodes : Fin 5 → Node p v :=
  ![⟨source p v, Iso.refl _⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap p v,
      BoundedFlatPerfectBinarySimplex.first p v⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap p v, BoundedFlatPerfectBinarySimplex.total p v⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap q w,
      sourceIso p v q w h ≪≫ BoundedFlatPerfectBinarySimplex.first q w⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap q w,
      sourceIso p v q w h ≪≫ BoundedFlatPerfectBinarySimplex.total q w⟩]

/--
The four-dimensional model simplex joining both binary normalization triangles at their common
source.
-/
def simplex : ModelSimplex (asSmallCategory (W Z))
    (asSmallCategory (W X)) 4 :=
  ModelSimplex.ofIsos (source p v) (fun i ↦ (nodes p v q w h i).1)
    (fun i ↦ (nodes p v q w h i).2)

/-- The face selecting vertices `0, 1, 2`, which carry the `p, v` binary normalization triangle. -/
def firstFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 2], by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
/-- The face selecting vertices `0, 3, 4`, which carry the `q, w` binary normalization triangle. -/
def secondFace : ⦋2⦌ ⟶ ⦋4⦌ := SimplexCategory.Hom.mk ⟨![0, 3, 4], by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The first original whole binary normalization triangle. -/
theorem first_face : (simplex p v q w h).face firstFace =
    BoundedFlatPerfectBinarySimplex.simplex p v := by
  unfold simplex BoundedFlatPerfectBinarySimplex.simplex
  rw [ModelSimplex.ofIsos_face]
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · fin_cases i <;> rfl
  · intro i j f
    fin_cases i <;> fin_cases j <;> rfl

/-- The source, raw intermediate, and normalized target maps for the second route `q ≫ w`. -/
def secondVertices : Fin 3 → (asSmallCategory (W Z) ⟶
    asSmallCategory (W X)) :=
  ![BoundedFlatPerfectBinarySimplex.sourceMap q w,
    BoundedFlatPerfectBinarySimplex.intermediateMap q w,
    BoundedFlatPerfectBinarySimplex.targetMap q w]

/--
The identity, first normalization, and total normalization references for the three second-route
vertices.
-/
def secondReferences : ∀ i,
    (BoundedFlatPerfectBinarySimplex.sourceMap q w).hom.toFunctor ≅
      (secondVertices q w i).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (BoundedFlatPerfectBinarySimplex.first q w)
    (Fin.cases (BoundedFlatPerfectBinarySimplex.total q w) (fun i ↦ Fin.elim0 i)))

/--
The second-route vertices referenced to the fixed first-route source through the square-induced
isomorphism.
-/
def secondNodes (i : Fin 3) : Node p v :=
  ⟨secondVertices q w i, sourceIso p v q w h ≪≫ secondReferences q w i⟩

theorem second_reference : ModelSimplex.ofIsos (source p v)
    (fun i ↦ (secondNodes p v q w h i).1) (fun i ↦ (secondNodes p v q w h i).2) =
    BoundedFlatPerfectBinarySimplex.simplex q w :=
  ModelSimplex.ofIsos_change_reference (sourceIso p v q w h) (secondVertices q w)
    (secondReferences q w)

/-- The second whole native binary triangle retains its actual geometric equality transport. -/
theorem second_face : (simplex p v q w h).face secondFace =
    BoundedFlatPerfectBinarySimplex.simplex q w := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  refine (ModelSimplex.ofIsos_nodes_congr
    (fun i ↦ nodes p v q w h (secondFace.toOrderHom i)) (secondNodes p v q w h) ?_).trans
    (second_reference p v q w h)
  intro i
  fin_cases i
  · apply ModelSimplex.reference_node_eq (source_eq p v q w h)
    simp [sourceIso, secondReferences]
  · rfl
  · rfl

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectNativeSquareFiveSimplex
