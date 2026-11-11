/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorBoundaryDescent
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorSymbol
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PointPresentation

/-!
# Retraction of the diagonal Milnor symbol by the actual norm

The rational graph evaluates to its original Milnor tuple symbol. Additive
generation by tuple symbols gives the retraction in characteristic zero.
The base-field evaluation comparison transports it to integral motivic
cohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalMilnorEquivalence

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers DiagonalCycleSymbols
open DiagonalPointPresentation DiagonalMilnorSymbol DiagonalMilnorBoundaryDescent

variable (k : Type u) [Field k] [CharZero k] (q : ℕ)

/-- The evaluator of the actual rational graph is the native ordered tuple symbol. -/
@[simp] theorem rawNorm_graphSymbol (a : Fin q → kˣ) :
    rawNorm k q (graphSymbol k q a) = milnorKTupleSymbol a :=
  (rawNorm_cycleClass k q ((Cor.graphFunctor k).map (rationalTuple k q a))).trans
    (cycleValue_rationalTuple a)

/-- Norm evaluation is a left inverse to the original rational graph map. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/MilnorNormRetraction.lean:21-54"
  "adaptation" "The native Milnor norm evaluates the actual graph symbol"]
theorem rawNorm_rawSymbol (x : MilnorKTheory k q) :
    rawNorm k q (rawSymbol k q x) = x := by
  have h : (rawNorm k q).comp (rawSymbol k q) = AddMonoidHom.id (MilnorKTheory k q) := by
    apply milnorKTheory_addHom_ext
    intro a
    exact (congrArg (rawNorm k q) (rawSymbol_symbol k q a)).trans
      (rawNorm_graphSymbol k q a)
  exact DFunLike.congr_fun h x

/-- The original rational graph map is injective. -/
theorem rawSymbol_injective : Function.Injective (rawSymbol k q) :=
  Function.LeftInverse.injective (rawNorm_rawSymbol k q)

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The norm is a left inverse of the original integral motivic symbol. -/
theorem motivicNorm_motivicSymbol (x : MilnorKTheory k q) :
    motivicNorm k q (motivicSymbol k q x) = x := by
  calc
    _ = rawNorm k q
        (motivicRawBaseEvaluationComparison k q q (motivicSymbol k q x)) :=
      motivicNorm_comparison k q (motivicSymbol k q x)
    _ = rawNorm k q (rawSymbol k q x) :=
      congrArg (rawNorm k q) (motivicSymbol_comparison k q x)
    _ = x := rawNorm_rawSymbol k q x

end AlgebraicGeometry.MotivicCohomology.DiagonalMilnorEquivalence
