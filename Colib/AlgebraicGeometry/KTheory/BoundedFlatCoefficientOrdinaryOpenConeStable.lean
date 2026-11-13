/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenKZeroExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenNull
public import Colib.KTheory.Waldhausen.Iterated.ModelStableKMap
public import Colib.KTheory.Waldhausen.Iterated.ConeFiberExcision
public import Colib.Topology.Prespectrum.ConeDescCofinality
public import Colib.Topology.Prespectrum.ConeDiagramDescent
/-! # Original ordinary restriction cone and the actual quotient grading

The original K-zero exactness, signed Model connectivity and ordinary cofinality prove
stability of the actual initial cone descent, retaining its whole chosen null.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Original positive graded K-groups identify with the same Model's positive stable groups. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:43"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientGradedOpen_stable_succ_subsingleton (a : Under R) (n : ℕ) :
    Subsingleton (stableHomotopyGroup (prespectrum (boundedAboveFlatCoefficientGradedOpenModel f a))
      ((n + 1 : ℕ) : ℤ)) := by
  let : Subsingleton ((boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.K (n + 1)) :=
    boundedAboveFlatCoefficientGradedOpen_K_succ_subsingleton f a n
  let e : Additive ((boundedAboveFlatCoefficientFullOpenGrading f a).coarseStructure.K (n + 1)) ≃+
      stableHomotopyGroup (prespectrum (boundedAboveFlatCoefficientGradedOpenModel f a))
        ((n + 1 : ℕ) : ℤ) :=
    levelOneStableEquiv (prespectrum (boundedAboveFlatCoefficientGradedOpenModel f a))
      (prespectrum_isOmega (boundedAboveFlatCoefficientGradedOpenModel f a)) (n + 1)
  exact e.symm.injective.subsingleton

/-- Actual Model connectivity gives negative signed stable vanishing without compactness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:56"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientGradedOpen_stable_neg_subsingleton
    (a : Under R) (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedAboveFlatCoefficientGradedOpenModel f a)) d) :=
  prespectrum_stableHomotopyGroup_neg_subsingleton
    (boundedAboveFlatCoefficientGradedOpenModel f a) d hd

/-- The actual pointwise graded Model has no signed stable classes outside degree zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:63"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientGradedOpen_stable_subsingleton
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup
      (prespectrum (boundedAboveFlatCoefficientGradedOpenModel f a)) d) := by
  by_cases hn : d < 0
  · exact boundedAboveFlatCoefficientGradedOpen_stable_neg_subsingleton f a d hn
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    rw [he, hp]
    exact boundedAboveFlatCoefficientGradedOpen_stable_succ_subsingleton f a (d.toNat - 1)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Honest original K-zero exactness identifies every specified native cone descent at zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:77"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientOpenConeDesc_stable_zero_bijective (a : Under R)
    (N : Homotopy
      ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a ≫
        (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a)
      (zeroHom ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a)
        ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a))) :
    Function.Bijective ((stableHomotopyFunctor 0).map
      (mappingConeDesc
        ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a) N)) := by
  let W := boundedAboveFlatCoefficientOpenModel f a
  let V := (boundedAboveFlatCoefficientFullOpenModelFunctor f).obj a
  let G := boundedAboveFlatCoefficientGradedOpenModel f a
  let fr : W ⟶ V := boundedAboveFlatCoefficientOpenRestrictionModelMap f a
  let fq : V ⟶ G := boundedAboveFlatCoefficientOpenGradingModelMap f a
  let r := prespectrumMap fr
  let q := prespectrumMap fq
  let eW := levelOneStableEquiv (prespectrum W) (prespectrum_isOmega W) 0
  let eV := levelOneStableEquiv (prespectrum V) (prespectrum_isOmega V) 0
  let eG := levelOneStableEquiv (prespectrum G) (prespectrum_isOmega G) 0
  have nq (x : V.obj.waldhausen.K 0) :
      (stableHomotopyFunctor 0).map q (eV (Additive.ofMul x)) =
        eG (Additive.ofMul (KMap fq.hom.isExact 0 x)) :=
    (smallModelKStableEquiv_naturality fq 0 x).symm
  have hf : IsStableEquivalence (mappingConeFiberComparison r) :=
    prespectrum_mappingConeFiberComparison_isStableEquivalence r
  let : Subsingleton (stableHomotopyGroup (prespectrum W) (-1)) :=
    prespectrum_stableHomotopyGroup_neg_subsingleton W (-1) (by omega)
  change Function.Bijective ((stableHomotopyFunctor 0).map (mappingConeDesc r q N))
  apply mappingConeDesc_stable_zero_bijective r q N hf
  · intro x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := eV.surjective x
      have hz : KMap fq.hom.isExact 0 z.toMul = 1 := by
        have h := eG.injective ((nq z.toMul).symm.trans (hx.trans (map_zero eG).symm))
        exact congrArg Additive.toMul h
      have he : (KMap fr.hom.isExact 0).range = (KMap fq.hom.isExact 0).ker :=
        boundedAboveFlatCoefficientOpenGrading_KMap_zero_range_ker f a
      have hz' : z.toMul ∈ (KMap fr.hom.isExact 0).range := by
        rw [he]
        exact hz
      obtain ⟨w, hw⟩ := hz'
      exact ⟨eW (Additive.ofMul w),
        (smallModelKStableEquiv_naturality fr 0 w).symm.trans
          (congrArg (fun y ↦ eV (Additive.ofMul y)) hw)⟩
    · rintro ⟨z, hz⟩
      have hc : (stableHomotopyFunctor 0).map r ≫ (stableHomotopyFunctor 0).map q = 0 :=
        ((stableHomotopyFunctor 0).map_comp r q).symm.trans
          ((N.stableHomotopyMap_eq 0).trans
            (stableHomotopyMap_zero (prespectrum W) (prespectrum G) 0))
      exact (congrArg ((stableHomotopyFunctor 0).map q) hz).symm.trans
        (ConcreteCategory.congr_hom hc z)
  · exact prespectrumMap_stable_nonnegative_surjective fq 0
      (boundedAboveFlatCoefficientOpenGrading_KMap_zero_surjective f a)

variable [QuasiSeparatedSpace Q.left]

/-- Original r cofinality and Model connectivity prove injectivity in every signed degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:135"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientOpenRestriction_stable_injective (a : Under R) (d : ℤ) :
    Function.Injective ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)) := by
  by_cases hd : d < 0
  · intro x y _
    exact (prespectrum_stableHomotopyGroup_neg_subsingleton
      (boundedAboveFlatCoefficientOpenModel f a) d hd).elim x y
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    exact prespectrumMap_stable_nonnegative_injective
      (boundedAboveFlatCoefficientOpenRestrictionModelMap f a) d.toNat
      (boundedAboveFlatCoefficientOpenRestriction_KMap_injective f a d.toNat)

/-- The same original signed r map is surjective away from its honest degree-zero image. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:149"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientOpenRestriction_stable_surjective_of_ne_zero
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Function.Surjective ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)) := by
  by_cases hn : d < 0
  · intro x
    exact ⟨0, (prespectrum_stableHomotopyGroup_neg_subsingleton
      ((boundedAboveFlatCoefficientFullOpenModelFunctor f).obj a) d hn).elim _ _⟩
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    have hs : Function.Surjective
        (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) d.toNat) := by
      rw [hp]
      exact (boundedAboveFlatCoefficientOpenRestriction_KMap_succ_bijective f a
        (d.toNat - 1)).surjective
    rw [he]
    exact prespectrumMap_stable_nonnegative_surjective
      (boundedAboveFlatCoefficientOpenRestrictionModelMap f a) d.toNat hs

/-- Genuine Model excision and original r/q facts prove every specified descent stable. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:169"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientOpenConeDesc_isStableEquivalence (a : Under R)
    (N : Homotopy
      ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a ≫
        (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a)
      (zeroHom ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a)
        ((boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a))) :
    IsStableEquivalence
      (mappingConeDesc
        ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a) N) := by
  apply mappingConeDesc_isStableEquivalence_of_cofinality
  · exact prespectrum_mappingConeFiberComparison_isStableEquivalence
      (prespectrumMap (boundedAboveFlatCoefficientOpenRestrictionModelMap f a))
  · exact boundedAboveFlatCoefficientOpenRestriction_stable_injective f a
  · exact boundedAboveFlatCoefficientOpenRestriction_stable_surjective_of_ne_zero f a
  · exact boundedAboveFlatCoefficientGradedOpen_stable_subsingleton f a
  · exact boundedAboveFlatCoefficientOpenConeDesc_stable_zero_bijective f a N

omit [QuasiSeparatedSpace Q.left] in
/-- The actual initial cone comparison specializes to the unchanged canonical whole null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:188"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
def boundedAboveFlatCoefficientOpenConeComparison (a : Under R) :
    mappingCone ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a) ⟶
      (boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f).obj a :=
  mappingConeDesc ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a)
    ((boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a)
    ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a)

omit [QuasiSeparatedSpace Q.left] in
/-- The original cone inclusion face is exactly the actual q component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:197"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null", reassoc]
theorem boundedAboveFlatCoefficientOpenConeComparison_inclusion (a : Under R) :
    mappingConeInclusion
        ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a) ≫
        boundedAboveFlatCoefficientOpenConeComparison f a =
      (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f).app a :=
  mappingConeInclusion_desc _ _ _

omit [QuasiSeparatedSpace Q.left] in
/-- Every original cone cylinder point retains the same canonical whole-null time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:206"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientOpenConeComparison_cylinder (a : Under R)
    (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    (boundedAboveFlatCoefficientOpenConeComparison f a).map n
      (ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).point n)
        (((boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f).obj a).point n)
        (((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a).map n)
        (s, x)) =
      ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x) := rfl

/-- The canonical whole-null specialization is stable in all integer degrees. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:218"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientOpenConeComparison_isStableEquivalence (a : Under R) :
    IsStableEquivalence (boundedAboveFlatCoefficientOpenConeComparison f a) :=
  boundedAboveFlatCoefficientOpenConeDesc_isStableEquivalence f a
    ((boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a)

omit [QuasiSeparatedSpace Q.left] in
/-- The unchanged whole null supplies the actual coefficient-natural cone comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:225"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
def boundedAboveFlatCoefficientOpenConeComparisonTransformation :
    mappingConeDiagram (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f) ⟶
      boundedAboveFlatCoefficientGradedOpenPrespectrumFunctor f :=
  mappingConeDescTransformation
    (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedAboveFlatCoefficientOpenGradingPrespectrumTransformation f)
    (fun a ↦ (boundedAboveFlatCoefficientOpenGradingDiagramNull f).homotopy a)
    (fun {_ _} g ↦ (boundedAboveFlatCoefficientOpenGradingDiagramNull f).naturality g)

omit [QuasiSeparatedSpace Q.left] in
/-- Each coefficient component retains precisely the original canonical cone descent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientOpenConeStable.lean:235"
  "adaptation" "Original actual ordinary cone, signed groups and same chosen null"]
theorem boundedAboveFlatCoefficientOpenConeComparisonTransformation_app (a : Under R) :
    (boundedAboveFlatCoefficientOpenConeComparisonTransformation f).app a =
      boundedAboveFlatCoefficientOpenConeComparison f a := rfl

end AlgebraicGeometry.Scheme.Modules
