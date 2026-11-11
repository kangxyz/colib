/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CoordinateInsertion
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.SteinbergBound
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Milnor
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Descent

/-!
# The all-weight diagonal Milnor symbol

The graph of an ordered tuple gives a multilinear class in the actual raw
diagonal homology. Insertion propagates the weight-two Steinberg relation to
the adjacent pairs of the native Milnor presentation. The field evaluation
equivalence transports the resulting homomorphism to integral hypercohomology.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalMilnorSymbol

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers DiagonalCycleSymbols NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- The one-entry graph is the existing weight-one graph class. -/
theorem graphSymbol_one_weight (a : Fin 1 → kˣ) :
    graphSymbol k 1 a = WeightOne.graphUnitClass k (a 0) := by
  have h : rationalTuple k 1 a = WeightOne.rationalPoint k (a 0) := by
    apply SmoothSite.torusPower_hom_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [rationalTuple_coordinate]
    change _ = (smoothUnitPoint (𝟙 (Spec (.of k))) (a 0) ≫
      (SmoothSite.torusPowerOneIso (Spec (.of k))).inv) ≫
        (SmoothSite.torusPowerOneIso (Spec (.of k))).hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (fun f => cycleClass k 1 ((Cor.graphFunctor k).map f)) h).trans
    (cycleClass_one k _)

/-- Multilinearity and insertion give the native Milnor symbol relations for actual graphs. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/MilnorSymbol.lean:41-48"
  "adaptation" "Coordinate additivity and Steinberg for the actual diagonal graph classes"]
theorem graphSymbol_isSymbolMap [CharZero k] (q : ℕ) : IsMilnorKSymbolMap (graphSymbol k q) where
  map_mul := graphSymbol_mul k q
  steinberg a i j hij hab :=
    DiagonalCoordinateInsertion.graphSymbol_steinberg_of_two k
      (DiagonalSteinbergBound.graphSymbol_steinberg k) q a i j (by
        intro h
        have hv := congrArg Fin.val h
        omega) hab

variable [CharZero k]

/-- The graph map descends through the native Milnor group into the raw diagonal homology. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/MilnorSymbol.lean:50-57"
  "adaptation" "The graph map descends through the native homogeneous Steinberg quotient"]
def rawSymbol (q : ℕ) : MilnorKTheory k q →+ (motivicRawBaseComplex k q).homology q :=
  (graphSymbol_isSymbolMap k q).lift.toAddMonoidHom

/-- The raw symbol retains the literal ordered rational graph. -/
@[simp] theorem rawSymbol_symbol (q : ℕ) (a : Fin q → kˣ) :
    rawSymbol k q (milnorKTupleSymbol a) = graphSymbol k q a :=
  (graphSymbol_isSymbolMap k q).lift_symbol a

/-- In weight one, the raw symbol followed by the norm gives the native units equivalence. -/
theorem rawSymbol_one_comparison (x : MilnorKTheory k 1) :
    WeightOne.homologyNorm k (rawSymbol k 1 x) = milnorKTheoryOneAddEquiv k x := by
  have h : (WeightOne.homologyNorm k).comp (rawSymbol k 1) =
      (milnorKTheoryOneAddEquiv k).toAddMonoidHom := by
    apply milnorKTheory_addHom_ext
    intro a
    change WeightOne.rawComparisonNorm k (rawSymbol k 1 (milnorKTupleSymbol a)) =
      milnorKTheoryOneAddEquiv k (milnorKTupleSymbol a)
    rw [rawSymbol_symbol, graphSymbol_one_weight, WeightOne.rawComparisonNorm_graphUnitClass]
    apply (milnorKTheoryOneAddEquiv k).symm.injective
    rw [AddEquiv.symm_apply_apply]
    apply Subtype.ext
    simp only [coe_milnorKTupleSymbol, List.ofFn_succ, List.ofFn_zero,
      milnorKSymbolProd_singleton, coe_milnorKTheoryOneAddEquiv_symm, milnorKSymbol_eq_mk']
  exact DFunLike.congr_fun h x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The all-weight symbol in integral motivic cohomology at the base field. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/MilnorSymbol.lean:117-131"
  "adaptation" "The same raw graph map transported to the original integral hypercohomology"]
def motivicSymbol (q : ℕ) : MilnorKTheory k q →+
    motivicCohomology k q q (SmoothSite.base (Spec (.of k))) :=
  (motivicRawBaseEvaluationComparison k q q).symm.toAddMonoidHom.comp (rawSymbol k q)

/-- The field evaluation comparison sends the derived symbol to the raw symbol. -/
theorem motivicSymbol_comparison (q : ℕ) (x : MilnorKTheory k q) :
    motivicRawBaseEvaluationComparison k q q (motivicSymbol k q x) = rawSymbol k q x :=
  (motivicRawBaseEvaluationComparison k q q).apply_symm_apply _

/-- Each tuple symbol maps to its original graph class under the integral comparison. -/
@[simp] theorem motivicSymbol_symbol (q : ℕ) (a : Fin q → kˣ) :
    motivicSymbol k q (milnorKTupleSymbol a) =
      (motivicRawBaseEvaluationComparison k q q).symm (graphSymbol k q a) := by
  change (motivicRawBaseEvaluationComparison k q q).symm
    (rawSymbol k q (milnorKTupleSymbol a)) = _
  rw [rawSymbol_symbol]

/-- The integral forward map in weight one agrees with the existing Milnor equivalence. -/
theorem motivicSymbol_one_comparison (x : MilnorKTheory k 1) :
    motivicSymbol k 1 x = WeightOne.milnorEquiv k x := by
  apply (WeightOne.weightOneEquiv k).injective
  change WeightOne.homologyNorm k
      (motivicRawBaseEvaluationComparison k 1 1 (motivicSymbol k 1 x)) =
    WeightOne.weightOneEquiv k ((WeightOne.weightOneEquiv k).symm (milnorKTheoryOneAddEquiv k x))
  calc
    _ = WeightOne.homologyNorm k (rawSymbol k 1 x) :=
      congrArg (WeightOne.homologyNorm k) (motivicSymbol_comparison k 1 x)
    _ = milnorKTheoryOneAddEquiv k x := rawSymbol_one_comparison k x
    _ = _ := ((WeightOne.weightOneEquiv k).apply_symm_apply _).symm

end AlgebraicGeometry.MotivicCohomology.DiagonalMilnorSymbol
