/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.FieldCycleEvaluation
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.SheafComparison
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The actual raw-field map induced by the weight-one sheaf comparison

The map is the transfer-natural raw/sheaf field isomorphism followed by exact
base evaluation of the actual geometric norm, units contraction and signed
shift. This isolates the concrete map whose degree-one unit-coordinate formula
must identify it with the literal support determinant norm.

The target is kept as the actual evaluated shifted Gm complex. No arbitrary
additive equivalence with the unit group is substituted for the missing
coordinate and graph comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The actual Gm target, retaining the existing signed shift by minus one. -/
abbrev shiftedUnitsSheafComplex :
    CochainComplex (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) ℤ :=
  ((CochainComplex.singleFunctor _ 0).obj (largeUnitsSheaf (Spec (.of k))))⟦(-1 : ℤ)⟧

/-- Native base evaluation of that precise shifted units complex. -/
def shiftedUnitsBaseComplex : CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  (((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).obj
      (shiftedUnitsSheafComplex k)

/-- The genuine raw cochain map, with the geometric norm and all original signs retained. -/
def rawWeightOneComparison : motivicRawBaseComplex k 1 ⟶ shiftedUnitsBaseComplex k :=
  (motivicRawBaseComplexIso k 1).hom ≫
    (((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
      (op (base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).map
        (weightOneSheafComparison k)

/-- Each component is the exact raw/sheaf unit followed by the original sheaf component. -/
theorem rawWeightOneComparison_f (i : ℤ) :
    (rawWeightOneComparison k).f i =
      (motivicRawBaseComplexIso k 1).hom.f i ≫
        ((weightOneSheafComparison k).f i).hom.app (op (base (Spec (.of k)))) := rfl

/-- Exact field evaluation preserves the concrete sheaf quasi-isomorphism. -/
instance rawWeightOneComparison_quasiIso : QuasiIso (rawWeightOneComparison k) := by
  let E := (sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))
  have hE : E.PreservesHomology := sheafSections_base_preservesHomology k
  have hmap : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map
      (weightOneSheafComparison k)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology (weightOneSheafComparison k) E
  exact _root_.quasiIso_comp (motivicRawBaseComplexIso k 1).hom
    ((E.mapHomologicalComplex (.up ℤ)).map (weightOneSheafComparison k)) (hφ' := hmap)

/-- The actual comparison induces an isomorphism, still with its precise shifted target. -/
def rawWeightOneHomologyIso (p : ℤ) :
    (motivicRawBaseComplex k 1).homology p ≅ (shiftedUnitsBaseComplex k).homology p :=
  asIso (HomologicalComplex.homologyMap (rawWeightOneComparison k) p)

/-- The forward homology map is literally the map induced by the geometric cochain composite. -/
theorem rawWeightOneHomologyIso_hom (p : ℤ) :
    (rawWeightOneHomologyIso k p).hom =
      HomologicalComplex.homologyMap (rawWeightOneComparison k) p := rfl

/-- The actual cycle inclusion and quotient determine the comparison on representatives. -/
theorem rawWeightOneComparison_class (p : ℤ) (x : (motivicRawBaseComplex k 1).cycles p) :
    (rawWeightOneHomologyIso k p).hom ((motivicRawBaseComplex k 1).homologyπ p x) =
      (shiftedUnitsBaseComplex k).homologyπ p
        (HomologicalComplex.cyclesMap (rawWeightOneComparison k) p x) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (rawWeightOneComparison k) p) x

/-- Before passing to homology the map preserves the literal cycle inclusion. -/
theorem rawWeightOneComparison_cycles (p : ℤ)
    (x : (motivicRawBaseComplex k 1).cycles p) :
    (shiftedUnitsBaseComplex k).iCycles p
      (HomologicalComplex.cyclesMap (rawWeightOneComparison k) p x) =
    (rawWeightOneComparison k).f p ((motivicRawBaseComplex k 1).iCycles p x) :=
  ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (rawWeightOneComparison k) p) x

/-- Evaluation commutes with the actual shift and the actual single-complex functor. -/
def shiftedUnitsBaseComplexIso : shiftedUnitsBaseComplex k ≅
    ((CochainComplex.singleFunctor AddCommGrpCat.{u + 1} 0).obj
      ((largeUnitsPresheaf (Spec (.of k))).obj (op (base (Spec (.of k))))))⟦(-1 : ℤ)⟧ := by
  let E := (sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))
  exact (E.mapCochainComplexShiftIso (-1)).app
      ((CochainComplex.singleFunctor _ 0).obj (largeUnitsSheaf (Spec (.of k)))) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app
        (largeUnitsSheaf (Spec (.of k))))

/-- The target's degree-one homology is its literal base section group, with the native shift. -/
def shiftedUnitsBaseHomologyIso : (shiftedUnitsBaseComplex k).homology 1 ≅
    (largeUnitsPresheaf (Spec (.of k))).obj (op (base (Spec (.of k)))) := by
  let A := (largeUnitsPresheaf (Spec (.of k))).obj (op (base (Spec (.of k))))
  let K := (CochainComplex.singleFunctor AddCommGrpCat.{u + 1} 0).obj A
  exact HomologicalComplex.homologyMapIso (shiftedUnitsBaseComplexIso k) 1 ≪≫
    (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1}
      (-1) 1 0 (by decide)).app K ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A

/-- Native ΓSpec and ULift identifications of the exact shifted target, not a chosen group map. -/
def shiftedUnitsBaseHomologyEquiv : (shiftedUnitsBaseComplex k).homology 1 ≃+ Additive kˣ :=
  ((shiftedUnitsBaseHomologyIso k) ≪≫
    NativeTorusPolynomial.specUnitsIso (𝟙 (Spec (.of k)))).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift

/-- The norm candidate induced by the specified geometric sheaf map and fixed ΓSpec coordinates. -/
def rawComparisonNorm : (motivicRawBaseComplex k 1).homology 1 →+ Additive kˣ :=
  (shiftedUnitsBaseHomologyEquiv k).toAddMonoidHom.comp
    (rawWeightOneHomologyIso k 1).hom.hom

/-- The specified comparison map is bijective; identifying its point formula remains separate. -/
theorem rawComparisonNorm_bijective : Function.Bijective (rawComparisonNorm k) :=
  (shiftedUnitsBaseHomologyEquiv k).bijective.comp
    (rawWeightOneHomologyIso k 1).addCommGroupIsoToAddEquiv.bijective

/-- The exact formula for a cycle, exposing the only component that still needs normalization. -/
theorem rawComparisonNorm_class (x : (motivicRawBaseComplex k 1).cycles 1) :
    rawComparisonNorm k ((motivicRawBaseComplex k 1).homologyπ 1 x) =
      shiftedUnitsBaseHomologyEquiv k ((shiftedUnitsBaseComplex k).homologyπ 1
        (HomologicalComplex.cyclesMap (rawWeightOneComparison k) 1 x)) := by
  change shiftedUnitsBaseHomologyEquiv k
    ((rawWeightOneHomologyIso k 1).hom ((motivicRawBaseComplex k 1).homologyπ 1 x)) = _
  rw [rawWeightOneComparison_class]

variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual derived sheaf map, before any unit-coordinate identification. -/
def derivedWeightOneComparison (p : ℤ) :
    AddCommGrpCat.of (motivicCohomology k p 1 (base (Spec (.of k)))) ⟶
      (Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyPresheaf.{w, u + 1}
        (nisnevichTopology (Spec (.of k))) (shiftedUnitsSheafComplex k) p).obj
          (op (base (Spec (.of k)))) :=
  ((Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyPresheafFunctor.{w, u + 1}
    (nisnevichTopology (Spec (.of k))) p).map (weightOneSheafComparison k)).app
      (op (base (Spec (.of k))))

/-- Derived and raw comparisons use the same coefficient map, rather than a chosen equivalence. -/
theorem rawWeightOneComparison_derived (p : ℤ)
    (x : motivicCohomology k p 1 (base (Spec (.of k)))) :
    hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) p
        (derivedWeightOneComparison k p x) =
      (rawWeightOneHomologyIso k p).hom (motivicRawBaseEvaluationComparison k p 1 x) := by
  erw [rawWeightOneHomologyIso_hom, rawWeightOneComparison,
    HomologicalComplex.homologyMap_comp]
  change hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) p
      (derivedWeightOneComparison k p x) =
    HomologicalComplex.homologyMap
      ((((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
        (op (base (Spec (.of k))))).mapHomologicalComplex (.up ℤ)).map
          (weightOneSheafComparison k)) p
      (HomologicalComplex.homologyMap (motivicRawBaseComplexIso k 1).hom p
        (HomologicalComplex.homologyMap (motivicRawBaseComplexIso k 1).inv p
          (motivicBaseEvaluationComparison k p 1 x)))
  have hcancel :
      HomologicalComplex.homologyMap (motivicRawBaseComplexIso k 1).hom p
        (HomologicalComplex.homologyMap (motivicRawBaseComplexIso k 1).inv p
          (motivicBaseEvaluationComparison k p 1 x)) =
        motivicBaseEvaluationComparison k p 1 x :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.homologyMapIso (motivicRawBaseComplexIso k 1) p).inv_hom_id _
  rw [hcancel]
  exact hypercohomologyBaseFieldAddEquiv_naturality k (weightOneSheafComparison k) p x

end AlgebraicGeometry.MotivicCohomology.WeightOne
