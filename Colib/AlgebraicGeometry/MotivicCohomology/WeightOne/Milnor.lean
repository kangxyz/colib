/-
Copyright (c) 2026 Motivic Cohomology contributors and Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.IntegralEquivalence
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeOne

/-!
# The weight-one diagonal Milnor comparison

The native first Milnor group and integral motivic cohomology at the base field
are compared through their canonical identifications with the unit group.
The forward map sends the singleton symbol to the actual integral rational graph class.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The native first Milnor group is the original integral weight-one group of the base field. -/
@[colib_tag "COL-1023", colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/Equivalence.lean:291-307" "adaptation"
  "Weight one through the native Milnor-to-units and integral geometric norm equivalences"]
def milnorEquiv : MilnorKTheory k 1 ≃+ motivicCohomology k 1 1 (base (Spec (.of k))) :=
  (milnorKTheoryOneAddEquiv k).trans (weightOneEquiv k).symm

/-- The singleton Milnor symbol is sent to the integral class of its rational graph. -/
@[simp, colib_tag "COL-1023", colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/MilnorSymbol.lean:59-72" "adaptation"
  "The singleton symbol retains the literal rational graph in the integral group"]
theorem milnorEquiv_tupleSymbol (a : Fin 1 → kˣ) :
    milnorEquiv k (milnorKTupleSymbol a) = integralGraphUnitClass k (a 0) := by
  have ha : milnorKTupleSymbol a =
      (milnorKTheoryOneAddEquiv k).symm (Additive.ofMul (a 0)) := by
    apply Subtype.ext
    simp only [coe_milnorKTupleSymbol, List.ofFn_succ, List.ofFn_zero,
      milnorKSymbolProd_singleton, coe_milnorKTheoryOneAddEquiv_symm, milnorKSymbol_eq_mk']
  change (weightOneEquiv k).symm (milnorKTheoryOneAddEquiv k (milnorKTupleSymbol a)) = _
  simp only [ha, AddEquiv.apply_symm_apply, weightOneEquiv_symm_apply, toMul_ofMul]

/-- The inverse comparison is the actual geometric norm read as a first Milnor class. -/
@[simp] theorem milnorEquiv_symm_apply
    (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    (milnorEquiv k).symm x = (milnorKTheoryOneAddEquiv k).symm (motivicNorm k x) := rfl

end AlgebraicGeometry.MotivicCohomology.WeightOne
