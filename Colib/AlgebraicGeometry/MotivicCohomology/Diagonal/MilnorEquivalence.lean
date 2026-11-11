/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorNormRetraction
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PolynomialNormComparisonAll
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.SymbolFieldChange

/-!
# Milnor K-theory and integral diagonal motivic cohomology

The original rational graph map and the descended norm are inverse in
characteristic zero. Rational graphs give one inverse identity. The other
uses finite norm compatibility on the actual native prime cycles and extends
by signed additivity. The inverse consequently respects scalar pullback and
finite corestriction under the original base-field comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe w u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalMilnorEquivalence

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers DiagonalTopDegree DiagonalCycleSymbols
open DiagonalPointNorm DiagonalPointPresentation DiagonalMilnorSymbol DiagonalMilnorBoundaryDescent
open DiagonalCorestriction (corestriction integralCorestriction integralCorestriction_comparison)
open DiagonalPolynomialNormComparisonAll (rawSymbol_milnorKNorm)

section Equivalences

variable (k : Type u) [Field k] [CharZero k] (q : ℕ)

/-- Norm evaluation on a native coefficient-one point recovers its actual cycle class. -/
theorem rawSymbol_generatorValue (Z : Generator k q) :
    rawSymbol k q (generatorValue Z) =
      cycleClass k q (singleFiniteCorrespondence _ _ Z.val Z.property 1) := by
  let : CharZero (coordinateRing Z) :=
    charZero_of_injective_algebraMap (algebraMap k (coordinateRing Z)).injective
  let N := coordinateRing Z
  let a : Fin q → Nˣ := coordinateUnit Z
  let tr := corestriction (k := k) (E := N) q
  calc
    _ = tr (rawSymbol N q (milnorKTupleSymbol a)) :=
      rawSymbol_milnorKNorm (k := k) (E := N) q (milnorKTupleSymbol a)
    _ = tr (graphSymbol N q a) := congrArg tr (rawSymbol_symbol N q a)
    _ = _ := (cycleClass_generator Z).symm

/-- Norm evaluation followed by the graph map recovers the class of every signed point cycle. -/
theorem rawSymbol_cycleValue (α : point k ⟶ target k q) :
    rawSymbol k q (cycleValue k q α) = cycleClass k q α := by
  have h : (rawSymbol k q).comp (cycleValue k q) = cycleClass k q := by
    apply finiteCorrespondences.addHom_ext_one (𝟙 (Spec (.of k)))
      (SmoothSite.torusPower (Spec (.of k)) q).hom
    intro z hz
    let Z : Generator k q := ⟨z, hz⟩
    exact (congrArg (rawSymbol k q) (cycleValue_cycle Z)).trans
      (rawSymbol_generatorValue k q Z)
  exact DFunLike.congr_fun h α

/-- The rational graph map also inverts the norm on the actual raw diagonal group. -/
theorem rawSymbol_rawNorm (x : (motivicRawBaseComplex k q).homology q) :
    rawSymbol k q (rawNorm k q x) = x := by
  obtain ⟨α, rfl⟩ := DiagonalCorestriction.cycleClass_surjective k q x
  rw [rawNorm_cycleClass, rawSymbol_cycleValue]

/-- The original raw diagonal group with its actual symbol map and norm inverse. -/
def rawEquiv : MilnorKTheory k q ≃+ (motivicRawBaseComplex k q).homology q where
  toFun := rawSymbol k q
  invFun := rawNorm k q
  left_inv := rawNorm_rawSymbol k q
  right_inv := rawSymbol_rawNorm k q
  map_add' := map_add (rawSymbol k q)

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The motivic symbol is a left inverse of the original integral norm. -/
theorem motivicSymbol_motivicNorm
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicSymbol k q (motivicNorm k q x) = x := by
  apply (motivicRawBaseEvaluationComparison k q q).injective
  calc
    _ = rawSymbol k q (motivicNorm k q x) :=
      motivicSymbol_comparison k q (motivicNorm k q x)
    _ = rawSymbol k q (rawNorm k q (motivicRawBaseEvaluationComparison k q q x)) :=
      congrArg (rawSymbol k q) (motivicNorm_comparison k q x)
    _ = _ := rawSymbol_rawNorm k q (motivicRawBaseEvaluationComparison k q q x)

/-- Milnor K-theory is the original integral diagonal motivic cohomology in characteristic zero. -/
@[colib_tag "COL-1026",
  colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/MilnorEquivalence.lean:34-106"
  "adaptation" "The native graph symbol and signed point norm on original integral cohomology"]
def motivicEquiv : MilnorKTheory k q ≃+
    motivicCohomology k q q (SmoothSite.base (Spec (.of k))) where
  toFun := motivicSymbol k q
  invFun := motivicNorm k q
  left_inv := motivicNorm_motivicSymbol k q
  right_inv := motivicSymbol_motivicNorm k q
  map_add' := map_add (motivicSymbol k q)

/-- The comparison uses the original integral symbol. -/
@[simp] theorem motivicEquiv_apply (x : MilnorKTheory k q) :
    motivicEquiv k q x = motivicSymbol k q x := rfl

/-- The inverse comparison is the original integral norm. -/
@[simp] theorem motivicEquiv_symm_apply
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    (motivicEquiv k q).symm x = motivicNorm k q x := rfl

end Equivalences

section Naturality

open DiagonalFieldChange (fieldChange)
open DiagonalSymbolFieldChange (rawSymbol_fieldChange motivicFieldChange
  motivicFieldChange_rawComparison)

variable {k L : Type u} [Field k] [CharZero k] [Field L] [CharZero L] (q : ℕ)

/-- The raw inverse commutes with scalar pullback of the actual raw cycle classes. -/
theorem rawNorm_fieldChange (φ : k →+* L) (x : (motivicRawBaseComplex k q).homology q) :
    rawNorm L q (fieldChange φ q x) = milnorKTheoryMap φ q (rawNorm k q x) := by
  apply rawSymbol_injective L q
  calc
    _ = fieldChange φ q x := rawSymbol_rawNorm L q _
    _ = fieldChange φ q (rawSymbol k q (rawNorm k q x)) :=
      congrArg (fieldChange φ q) (rawSymbol_rawNorm k q x).symm
    _ = _ := rawSymbol_fieldChange φ q _

/-- The raw inverse takes finite corestriction to the original native Milnor norm. -/
theorem rawNorm_corestriction [Algebra k L] [FiniteDimensional k L]
    (x : (motivicRawBaseComplex L q).homology q) :
    rawNorm k q (corestriction (k := k) (E := L) q x) =
      milnorKNorm k L q (rawNorm L q x) := by
  apply rawSymbol_injective k q
  calc
    _ = corestriction (k := k) (E := L) q x := rawSymbol_rawNorm k q _
    _ = corestriction (k := k) (E := L) q (rawSymbol L q (rawNorm L q x)) :=
      congrArg (corestriction (k := k) (E := L) q) (rawSymbol_rawNorm L q x).symm
    _ = _ := (rawSymbol_milnorKNorm (k := k) (E := L) q _).symm

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The original integral inverse commutes with the derived field change. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/MilnorEquivalenceNaturality.lean:24-30,46-52"
  "adaptation" "Scalar pullback for the inverse of the actual diagonal comparison"]
theorem motivicNorm_fieldChange (φ : k →+* L)
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicNorm L q (motivicFieldChange φ q x) =
      milnorKTheoryMap φ q (motivicNorm k q x) := by
  rw [motivicNorm_comparison, motivicFieldChange_rawComparison,
    rawNorm_fieldChange, motivicNorm_comparison]

/-- Finite integral corestriction corresponds to the native Milnor norm under the inverse. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/MilnorEquivalenceNaturality.lean:32-39,54-60"
  "adaptation" "Finite corestriction for the inverse of the actual diagonal comparison"]
theorem motivicNorm_corestriction [Algebra k L] [FiniteDimensional k L]
    (x : motivicCohomology L q q (SmoothSite.base (Spec (.of L)))) :
    motivicNorm k q (integralCorestriction (k := k) (E := L) q x) =
      milnorKNorm k L q (motivicNorm L q x) := by
  rw [motivicNorm_comparison, integralCorestriction_comparison,
    rawNorm_corestriction, motivicNorm_comparison]

/-- The original integral symbol commutes with the native Milnor norm and finite corestriction. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/MilnorEquivalenceNaturality.lean:62-69"
  "adaptation" "Finite corestriction for the forward diagonal symbol"]
theorem motivicSymbol_finiteExtensionNorm [Algebra k L] [FiniteDimensional k L]
    (x : MilnorKTheory L q) :
    motivicSymbol k q (milnorKNorm k L q x) =
      integralCorestriction (k := k) (E := L) q (motivicSymbol L q x) := by
  apply (motivicRawBaseEvaluationComparison k q q).injective
  rw [motivicSymbol_comparison, integralCorestriction_comparison,
    motivicSymbol_comparison, rawSymbol_milnorKNorm]

end Naturality

attribute [colib_tag "COL-1026"]
  rawEquiv motivicNorm_motivicSymbol motivicSymbol_motivicNorm motivicNorm_fieldChange
  motivicNorm_corestriction motivicSymbol_finiteExtensionNorm
  DiagonalSymbolFieldChange.motivicSymbol_fieldChange

end AlgebraicGeometry.MotivicCohomology.DiagonalMilnorEquivalence
