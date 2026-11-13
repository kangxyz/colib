/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FieldChange
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorSymbol
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Field change of the diagonal Milnor symbol

For every field homomorphism, scalar pullback of the literal rational graph
applies the field map to every unit. The canonical field evaluation comparison
carries the resulting square on native Milnor groups to integral motivic
cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalSymbolFieldChange

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers DiagonalFieldChange DiagonalMilnorSymbol

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- Pullback commutes with the raw graph symbol on the native Milnor group. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/FieldChange.lean:137-151"
  "adaptation" "Naturality from the scalar pullback of the literal rational graphs"]
theorem rawSymbol_fieldChange (q : ℕ) (x : MilnorKTheory k q) :
    fieldChange φ q (rawSymbol k q x) = rawSymbol L q (milnorKTheoryMap φ q x) := by
  have h : (fieldChange φ q).comp (rawSymbol k q) =
      (rawSymbol L q).comp (milnorKTheoryMap φ q).toAddMonoidHom := by
    apply milnorKTheory_addHom_ext
    intro a
    change fieldChange φ q (rawSymbol k q (milnorKTupleSymbol a)) =
      rawSymbol L q (milnorKTheoryMap φ q (milnorKTupleSymbol a))
    simpa only [rawSymbol_symbol, milnorKTheoryMap_tupleSymbol, Function.comp_def] using
      graphSymbol_fieldChange φ q a
  exact DFunLike.congr_fun h x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The scalar pullback on integral diagonal motivic cohomology at the field point. -/
def motivicFieldChange (q : ℕ) :
    motivicCohomology k q q (SmoothSite.base (Spec (.of k))) →+
      motivicCohomology L q q (SmoothSite.base (Spec (.of L))) :=
  (motivicRawBaseEvaluationComparison L q q).symm.toAddMonoidHom.comp
    ((fieldChange φ q).comp (motivicRawBaseEvaluationComparison k q q).toAddMonoidHom)

/-- The derived field map retains the scalar pullback of the raw cycle classes. -/
theorem motivicFieldChange_rawComparison (q : ℕ)
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicRawBaseEvaluationComparison L q q (motivicFieldChange φ q x) =
      fieldChange φ q (motivicRawBaseEvaluationComparison k q q x) :=
  (motivicRawBaseEvaluationComparison L q q).apply_symm_apply _

/-- The integral diagonal Milnor symbol commutes with scalar pullback. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/FieldChange.lean:153-170"
  "adaptation" "The integral naturality square through the canonical raw field comparison"]
theorem motivicSymbol_fieldChange (q : ℕ) (x : MilnorKTheory k q) :
    motivicFieldChange φ q (motivicSymbol k q x) =
      motivicSymbol L q (milnorKTheoryMap φ q x) := by
  apply (motivicRawBaseEvaluationComparison L q q).injective
  rw [motivicFieldChange_rawComparison, motivicSymbol_comparison,
    motivicSymbol_comparison, rawSymbol_fieldChange]

/-- The scalar naturality square as an equality of additive maps. -/
theorem motivicSymbol_fieldChange_square (q : ℕ) :
    (motivicFieldChange φ q).comp (motivicSymbol k q) =
      (motivicSymbol L q).comp (milnorKTheoryMap φ q).toAddMonoidHom :=
  AddMonoidHom.ext (motivicSymbol_fieldChange φ q)

end AlgebraicGeometry.MotivicCohomology.DiagonalSymbolFieldChange
