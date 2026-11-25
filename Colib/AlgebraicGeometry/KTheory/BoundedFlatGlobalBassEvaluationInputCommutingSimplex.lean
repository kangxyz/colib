/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputParameter
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNodeTransport
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCommutingSquare

/-!
# Original evaluation composition faces of a commuting scheme square

The two five-node composition diagrams share their complete source and total-evaluation nodes.
The actual equality of scheme composites transports the second reference and its anchors. All
six remaining nodes, both full Model diagrams, and both original comparison surfaces survive in
one eight-node simplex with the first strict composite evaluation as its common reference.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCommutingSimplex
open GlobalSectionChangeIndex
variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
  (h : p ≫ v = q ≫ w)

/-- The common reference is the actual first strict composite followed by evaluation. -/
def sourceMap := InputSimplex.sourceMap p v

/-- The common total vertex retains evaluation of that same actual composite. -/
def totalMap := InputSimplex.totalMap p v

include h in
/-- The scheme-square equation identifies the original complete source Model arrows. -/
theorem source_eq : sourceMap p v = InputSimplex.sourceMap q w := by
  unfold sourceMap InputSimplex.sourceMap
  rw [h]

/-- The original comparison is transported only by the supplied equality of scheme composites. -/
def sourceIso : (sourceMap p v).hom.toFunctor ≅ (InputSimplex.sourceMap q w).hom.toFunctor :=
  eqToIso (congrArg (fun f => f.hom.toFunctor) (source_eq p v q w h))

/-- A node retains both its exact zero-preserving arrow and its original reference anchor. -/
abbrev Node :=
  Σ F : boundedAboveFlatGlobalSectionModelFunctor.obj (op C) ⟶
    asSmallCategory (boundedAboveFlatPerfectWaldhausen A.toRingedSpace),
  (sourceMap p v).hom.toFunctor ≅ F.hom.toFunctor

/-- The first five nodes have their original anchors without any transport. -/
def firstNodes (i : Fin 5) : Node p v :=
  ⟨InputSimplex.vertices p v i, InputSimplex.anchors p v i⟩

/-- The second five nodes use the actual source equality before each original anchor. -/
def secondNodes (i : Fin 5) : Node p v :=
  ⟨InputSimplex.vertices q w i,
    sourceIso p v q w h ≪≫ InputSimplex.anchors q w i⟩

/-- The first source is the whole actual reference node. -/
theorem firstNodes_zero : firstNodes p v 0 = ⟨sourceMap p v, Iso.refl _⟩ := rfl

/-- The first total includes the actual original evaluation isomorphism. -/
theorem firstNodes_one : firstNodes p v 1 =
    ⟨totalMap p v, evaluationComparisonIso (p ≫ v)⟩ := rfl

/-- Both source nodes agree including their dependent reference anchors. -/
theorem secondNodes_zero : secondNodes p v q w h 0 = firstNodes p v 0 := by
  apply ModelSimplex.reference_node_eq
    (congrArg (fun f => f.hom.toFunctor) (source_eq p v q w h).symm)
  simp only [sourceIso, InputSimplex.anchors, Fin.cases_zero, Iso.trans_refl,
    eqToIso.hom, eqToHom_trans, eqToHom_refl, Iso.refl_hom]
  rfl

/-- Both total-evaluation nodes agree as dependent nodes, preserving evaluation itself. -/
theorem secondNodes_one : secondNodes p v q w h 1 = firstNodes p v 1 := by
  have ha : InputSimplex.anchors q w 1 = evaluationComparisonIso (q ≫ w) := rfl
  rw [firstNodes_one]
  dsimp only [secondNodes]
  rw [ha]
  let S (a : A ⟶ C) := boundedAboveFlatGlobalSectionModelFunctor.map a.op ≫ evaluationModel (op A)
  let T (a : A ⟶ C) := evaluationModel (op C) ≫ evaluationRawMap a
  have hh := ModelSimplex.transportedReferenceNode_congr (sourceMap p v) S T
    (fun a => evaluationComparisonIso a) h.symm
    (congrArg (fun f => f.hom.toFunctor) (source_eq p v q w h)) rfl
  simpa only [ModelSimplex.transportedReferenceNode, sourceIso, eqToIso_refl,
    Iso.refl_trans, InputSimplex.vertices, Matrix.cons_val_one, Matrix.cons_val_zero,
    InputSimplex.totalMap, T, totalMap] using hh

/-- Eight complete nodes share exactly the common source and actual total evaluation. -/
def nodes : Fin 8 → Node p v :=
  ![firstNodes p v 0, firstNodes p v 1, firstNodes p v 2, firstNodes p v 3,
    firstNodes p v 4, secondNodes p v q w h 2, secondNodes p v q w h 3,
    secondNodes p v q w h 4]

/-- Every vertex is the retained original zero-preserving Model arrow. -/
def vertices (i : Fin 8) := (nodes p v q w h i).1

/-- Every anchor is the retained original isomorphism from the actual common reference. -/
def anchors (i : Fin 8) : (sourceMap p v).hom.toFunctor ≅ (vertices p v q w h i).hom.toFunctor :=
  (nodes p v q w h i).2

/-- One finite common-reference diagram contains both original composition diagrams. -/
def simplex : ModelSimplex (boundedAboveFlatGlobalSectionModelFunctor.obj (op C))
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen A.toRingedSpace)) 7 :=
  ModelSimplex.ofIsos (sourceMap p v) (vertices p v q w h) (anchors p v q w h)

/-- The first five-node face uses the actual original first composition order. -/
def firstFace : ⦋4⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 3, 4], by decide⟩

/-- The second five-node face shares both common nodes and keeps all three other nodes. -/
def secondFace : ⦋4⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 5, 6, 7], by decide⟩

/-- Every complete first-face node is unchanged, including its anchor. -/
theorem first_nodes (i : Fin 5) :
    nodes p v q w h (firstFace.toOrderHom i) = firstNodes p v i := by
  fin_cases i <;> rfl

/-- Every complete second-face node is the original node with actual source transport. -/
theorem second_nodes (i : Fin 5) :
    nodes p v q w h (secondFace.toOrderHom i) = secondNodes p v q w h i := by
  fin_cases i
  · exact (secondNodes_zero p v q w h).symm
  · exact (secondNodes_one p v q w h).symm
  · rfl
  · rfl
  · rfl

/-- The first-face arrows remain the actual original arrows. -/
theorem first_vertices (i : Fin 5) :
    vertices p v q w h (firstFace.toOrderHom i) = InputSimplex.vertices p v i :=
  congrArg Sigma.fst (first_nodes p v q w h i)

/-- The second-face arrows remain the actual original arrows. -/
theorem second_vertices (i : Fin 5) :
    vertices p v q w h (secondFace.toOrderHom i) = InputSimplex.vertices q w i :=
  congrArg Sigma.fst (second_nodes p v q w h i)

/-- The first anchors agree after the exact corresponding vertex identity. -/
theorem first_anchors (i : Fin 5) :
    anchors p v q w h (firstFace.toOrderHom i) ≪≫
      eqToIso (congrArg (fun f => f.hom.toFunctor) (first_vertices p v q w h i)) =
        InputSimplex.anchors p v i := by
  have hn := first_nodes p v q w h i
  have congr_anchor {N M : Node p v} (e : N = M) :
      N.2 ≪≫ eqToIso (congrArg (fun f => f.hom.toFunctor) (congrArg Sigma.fst e)) = M.2 := by
    subst M
    simp
  exact congr_anchor hn

/-- The second anchors retain their entire actual source transport. -/
theorem second_anchors (i : Fin 5) :
    anchors p v q w h (secondFace.toOrderHom i) ≪≫
      eqToIso (congrArg (fun f => f.hom.toFunctor) (second_vertices p v q w h i)) =
        sourceIso p v q w h ≪≫ InputSimplex.anchors q w i := by
  have hn := second_nodes p v q w h i
  have congr_anchor {N M : Node p v} (e : N = M) :
      N.2 ≪≫ eqToIso (congrArg (fun f => f.hom.toFunctor) (congrArg Sigma.fst e)) = M.2 := by
    subst M
    simp
  exact congr_anchor hn

/-- The entire first Model diagram equals its original composition simplex. -/
theorem first_face : (simplex p v q w h).face firstFace = InputSimplex.simplex p v := by
  rw [simplex, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (first_nodes p v q w h)

/-- The entire second Model diagram retains both shared nodes and every original arrow. -/
theorem second_face : (simplex p v q w h).face secondFace = InputSimplex.simplex q w := by
  rw [simplex, ModelSimplex.ofIsos_face]
  trans ModelSimplex.ofIsos (sourceMap p v)
    (fun i => (secondNodes p v q w h i).1) (fun i => (secondNodes p v q w h i).2)
  · exact ModelSimplex.ofIsos_nodes_congr _ _ (second_nodes p v q w h)
  · exact ModelSimplex.ofIsos_change_reference _ _ _

/-- The literal original composition word, embedded without changing either comparison clock. -/
def compositionParameter (α : ⦋4⦌ ⟶ ⦋7⦌) :
    ((edge (α.toOrderHom 0) (α.toOrderHom 1)).trans
      ((edge (α.toOrderHom 1) (α.toOrderHom 2)).trans
        (edge (α.toOrderHom 2) (α.toOrderHom 4)))).Homotopy
    ((edge (α.toOrderHom 0) (α.toOrderHom 3)).trans
      (edge (α.toOrderHom 3) (α.toOrderHom 4))) :=
  (InputParameter.reindexHomotopy α InputSimplex.compositionParameter).cast
    (by
      change InputParameter.reindexPath α
        ((edge 0 1).trans ((edge 1 2).trans (edge 2 4))) = _
      simp only [InputParameter.reindexPath_trans, InputParameter.reindexPath_edge])
    (by
      change InputParameter.reindexPath α ((edge 0 3).trans (edge 3 4)) = _
      simp only [InputParameter.reindexPath_trans, InputParameter.reindexPath_edge])

/-- Every native coordinate of the first original composition comparison is retained. -/
theorem first_native :
    HomotopyLift (simplex p v q w h) (compositionParameter firstFace)
      (evaluationCompositionRelHomotopy p v) := by
  have hl := InputParameter.reindex_native firstFace _ (simplex p v q w h)
    (first_face p v q w h) _ _ (InputSimplex.composition_native p v)
  intro n r s x
  exact hl n r s x

/-- Every native coordinate of the second original composition comparison is retained. -/
theorem second_native :
    HomotopyLift (simplex p v q w h) (compositionParameter secondFace)
      (evaluationCompositionRelHomotopy q w) := by
  have hl := InputParameter.reindex_native secondFace _ (simplex p v q w h)
    (second_face p v q w h) _ _ (InputSimplex.composition_native q w)
  intro n r s x
  exact hl n r s x

private theorem lift_of_native_levels
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {l m : Path a b} (J : l.Homotopy m)
    {f g f' g' : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    {H' K' : Homotopy f' g'} (M : H.RelHomotopy K) (N : H'.RelHomotopy K')
    (hM : HomotopyLift S J M)
    (he : ∀ n, (N.level n).toContinuousMap = (M.level n).toContinuousMap) :
    HomotopyLift S J N := by
  intro n r s x
  exact (hM n r s x).trans (DFunLike.congr_fun (he n).symm (r, (s, x)))

/-- The first common-prefix comparison preserves its whole original continuous family. -/
theorem first_comparison_level (n : ℕ) :
    ((InputCommutingSquare.compositionLegs p v).level n).toContinuousMap =
      ((evaluationCompositionRelHomotopy p v).level n).toContinuousMap := rfl

/-- Actual source transport leaves the second entire two-parameter native family unchanged. -/
theorem second_comparison_level (n : ℕ) :
    ((InputCommutingSquare.secondComparison p v q w h).level n).toContinuousMap =
      ((evaluationCompositionRelHomotopy q w).level n).toContinuousMap :=
  Homotopy.RelHomotopy.transportPrefix_level
    (fun r : A ⟶ C => sectionMap r ≫ evaluation A)
    (fun r : A ⟶ C => evaluation C ≫ boundedAboveFlatPerfectPullbackPrespectrumMap r)
    (fun r => evaluationComparison r) h (InputCommutingSquare.compositionLegs q w) n

/-- The first exact native comparison is lifted by its original five-node face. -/
theorem first_comparison_native :
    HomotopyLift (simplex p v q w h) (compositionParameter firstFace)
      (InputCommutingSquare.compositionLegs p v) :=
  lift_of_native_levels _ _ _ _ (first_native p v q w h) (first_comparison_level p v)

/-- The source-transported second comparison is lifted by its original five-node face. -/
theorem second_comparison_native :
    HomotopyLift (simplex p v q w h) (compositionParameter secondFace)
      (InputCommutingSquare.secondComparison p v q w h) :=
  lift_of_native_levels _ _ _ _ (second_native p v q w h) (second_comparison_level p v q w h)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputCommutingSimplex
