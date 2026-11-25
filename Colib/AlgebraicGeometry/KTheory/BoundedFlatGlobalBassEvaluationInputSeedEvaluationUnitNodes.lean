/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationUnitPasting
public import Colib.KTheory.Waldhausen.Iterated.SimplexIntertwiningLift
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveParameter

/-!
# Four complete nodes for the original global evaluation unit

The repeated Model arrows retain their distinct full reference anchors. The final anchor is
the original postwhiskered section unit followed by the actual evaluation comparison; its
alternative forward component is exactly the original normalized raw transformation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity CategoryTheory.Waldhausen Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationUnit
open GlobalSectionChangeIndex

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unchanged section pullback followed by actual target evaluation. -/
abbrev sourceMap := boundedAboveFlatGlobalSectionModelFunctor.map f.op ≫ evaluationModel (op X)

/-- Actual source evaluation followed by the unchanged normalized raw pullback. -/
abbrev targetMap := evaluationModel (op Y) ≫ evaluationRawMap f

/-- The original section identity action before evaluation. -/
def sectionUnit (r : (Γ(X, ⊤))ˣ) :=
  onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
    (boundedAboveFlatGlobalSectionUnit (op X) r)

/-- The full original unit anchor after actual target evaluation. -/
def unit (r : (Γ(X, ⊤))ˣ) : (sourceMap f).hom.toFunctor ≅ (sourceMap f).hom.toFunctor :=
  isoWhiskerRight (sectionUnit f r) (evaluationModel (op X)).hom.toFunctor

/-- All four original Model arrows, retaining separately anchored repeated arrows. -/
def vertices := SimplexIntertwiningLift.vertices
  (boundedAboveFlatGlobalSectionModelFunctor.map f.op) (evaluationRawMap f)
  (evaluationModel (op Y)) (evaluationModel (op X))

/-- The four full anchors used by the actual intertwining word. -/
def anchors (r : (Γ(X, ⊤))ˣ) :
    ∀ i, (sourceMap f).hom.toFunctor ≅ (vertices f i).hom.toFunctor :=
  SimplexIntertwiningLift.anchors (boundedAboveFlatGlobalSectionModelFunctor.map f.op)
    (evaluationRawMap f)
    (evaluationModel (op Y)) (evaluationModel (op X))
    (sectionUnit f r) (evaluationComparisonIso f)

/-- The exact complete dependent nodes, before nerve realization. -/
def nodes (r : (Γ(X, ⊤))ˣ) : Fin 4 → CommonReferenceNerve.Node (sourceMap f) :=
  fun i => ⟨vertices f i, anchors f r i⟩

/-- The initial node has the full identity reference. -/
theorem node_zero (r : (Γ(X, ⊤))ˣ) :
    nodes f r 0 = ⟨sourceMap f, Iso.refl _⟩ := rfl

/-- The old-unit endpoint retains its original postwhiskered anchor. -/
theorem node_one (r : (Γ(X, ⊤))ˣ) :
    nodes f r 1 = ⟨sourceMap f, unit f r⟩ := rfl

/-- The comparison endpoint retains the complete original evaluation isomorphism. -/
theorem node_two (r : (Γ(X, ⊤))ˣ) :
    nodes f r 2 = ⟨targetMap f, evaluationComparisonIso f⟩ := rfl

/-- The final full anchor is the original unit followed by actual evaluation. -/
theorem node_three (r : (Γ(X, ⊤))ˣ) :
    nodes f r 3 = ⟨targetMap f, unit f r ≪≫ evaluationComparisonIso f⟩ := rfl

/-- Its alternative forward component is the original normalized raw unit transformation. -/
theorem last_anchor_hom (r : (Γ(X, ⊤))ˣ) :
    (anchors f r 3).hom = (evaluationComparisonIso f).hom ≫
      whiskerLeft (evaluationModel (op Y)).hom.toFunctor (evaluationRawUnit f r) :=
  evaluation_unit_square f r

/-- The entire original first triangular face agrees as complete dependent nodes. -/
theorem first_nodes (r : (Γ(X, ⊤))ˣ) (i : Fin 3) :
    nodes f r (SimplexIntertwiningLift.firstFace.toOrderHom i) =
      ![⟨sourceMap f, Iso.refl _⟩, ⟨sourceMap f, unit f r⟩,
        ⟨targetMap f, unit f r ≪≫ evaluationComparisonIso f⟩] i := by
  fin_cases i <;> rfl

/-- The second triangular face retains the actual original comparison and shifted reference. -/
theorem second_nodes (r : (Γ(X, ⊤))ˣ) (i : Fin 3) :
    nodes f r (SimplexIntertwiningLift.secondFace.toOrderHom i) =
      ![⟨sourceMap f, Iso.refl _⟩, ⟨targetMap f, evaluationComparisonIso f⟩,
        ⟨targetMap f, unit f r ≪≫ evaluationComparisonIso f⟩] i := by
  fin_cases i <;> rfl

/-- The actual complete-node simplex of the original evaluation-unit square. -/
def simplex (r : (Γ(X, ⊤))ˣ) :=
  SimplexIntertwiningLift.simplex (boundedAboveFlatGlobalSectionModelFunctor.map f.op)
    (evaluationRawMap f)
    (evaluationModel (op Y)) (evaluationModel (op X))
    (sectionUnit f r) (evaluationComparisonIso f)

/-- The native simplex is literally the simplex of the four complete reference nodes. -/
theorem simplex_nodes (r : (Γ(X, ⊤))ˣ) :
    simplex f r = ModelSimplex.ofIsos (sourceMap f)
      (fun i => (nodes f r i).1) (fun i => (nodes f r i).2) := rfl

/-- The original two-triangle parameter follows its original reversal and concatenation clocks. -/
abbrev scalarParameter := SimplexIntertwiningLift.parameter

/-- The same whole square in the actual common-reference nerve. -/
def parameter (r : (Γ(X, ⊤))ˣ) :
    C(unitInterval × unitInterval,
      |nerve (Codiscrete (CommonReferenceNerve.Node (sourceMap f)))|) :=
  (CommonReferenceNerve.parameter (sourceMap f) (nodes f r)).comp
    scalarParameter.toContinuousMap

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationUnit
