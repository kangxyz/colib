/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenKZeroExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedStableGroups
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradingNull
public import Colib.KTheory.Waldhausen.Iterated.ModelStableKMap
public import Colib.KTheory.Waldhausen.Iterated.ConeFiberExcision
public import Colib.Topology.Prespectrum.ConeDescCofinality
public import Colib.Topology.Prespectrum.ConeDiagramDescent


/-!
# The actual supported native restriction cone and its original image grading

Supported joint-cylinder data prove positive graded K-vanishing. Original
Model connectivity gives negative stable vanishing, and the actual K-to-stable
dictionary transports supported r_Z cofinality. Honest supported K-zero image
exactness and q_Z surjectivity identify the initial cone descent at degree zero.

The signed cone theorem applies to every genuinely typed null. Its canonical
specialization retains the same coefficient-natural reversed zero-to-image
null, actual inclusion face and every original cylinder time. Stability uses
compact P, Q and auxiliary support complement T, and quasi-separated Q; the
construction and its naturality use only compact P and Q. No seed, telescope
or classical comparison is asserted.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Honest original K-zero exactness identifies every specified native cone descent at zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:82"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
theorem boundedAboveFlatCoefficientSupportedOpenConeDesc_stable_zero_bijective (a : Under R)
    (N : Homotopy
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a)
      (zeroHom ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)
        ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a))) :
    Function.Bijective ((stableHomotopyFunctor 0).map
      (mappingConeDesc
        ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
        f T).app a)
        ((boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a) N))
          := by
  let W := boundedAboveFlatCoefficientSupportedOpenModel f T a
  let V := (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T).obj a
  let G := boundedAboveFlatCoefficientSupportedGradedOpenModel f T a
  let fr : W ⟶ V := boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a
  let fq : V ⟶ G := boundedAboveFlatCoefficientSupportedOpenGradingModelMap f T a
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
        boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_range_ker f T a
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
      (boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_surjective f T a)

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- Original r cofinality and Model connectivity prove injectivity in every signed degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:141"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_stable_injective (a : Under R) (d : ℤ) :
    Function.Injective ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a))
        := by
  by_cases hd : d < 0
  · intro x y _
    exact (prespectrum_stableHomotopyGroup_neg_subsingleton
      (boundedAboveFlatCoefficientSupportedOpenModel f T a) d hd).elim x y
  · have he : d = (d.toNat : ℤ) := by omega
    rw [he]
    exact prespectrumMap_stable_nonnegative_injective
      (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a) d.toNat
      (boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_injective f T a d.toNat)

/-- The same original signed r map is surjective away from its honest degree-zero image. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:155"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
theorem boundedAboveFlatCoefficientSupportedOpenRestriction_stable_surjective_of_ne_zero
    (a : Under R) (d : ℤ) (hd : d ≠ 0) :
    Function.Surjective ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a))
        := by
  by_cases hn : d < 0
  · intro x
    exact ⟨0, (prespectrum_stableHomotopyGroup_neg_subsingleton
      ((boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T).obj a) d hn).elim _ _⟩
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    have hs : Function.Surjective
        (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) d.toNat) := by
      rw [hp]
      exact (boundedAboveFlatCoefficientSupportedOpenRestriction_KMap_succ_bijective f T a
        (d.toNat - 1)).surjective
    rw [he]
    exact prespectrumMap_stable_nonnegative_surjective
      (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a) d.toNat hs

/-- Genuine Model excision and original r/q facts prove every specified descent stable. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:175"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
theorem boundedAboveFlatCoefficientSupportedOpenConeDesc_isStableEquivalence (a : Under R)
    (N : Homotopy
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a ≫
        (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a)
      (zeroHom ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)
        ((boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a))) :
    IsStableEquivalence
      (mappingConeDesc
        ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
        f T).app a)
        ((boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a) N)
          := by
  apply mappingConeDesc_isStableEquivalence_of_cofinality
  · exact prespectrum_mappingConeFiberComparison_isStableEquivalence
      (prespectrumMap (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a))
  · exact boundedAboveFlatCoefficientSupportedOpenRestriction_stable_injective f T a
  · exact boundedAboveFlatCoefficientSupportedOpenRestriction_stable_surjective_of_ne_zero f T a
  · exact boundedAboveFlatCoefficientSupportedGradedOpen_stable_subsingleton f T a
  · exact boundedAboveFlatCoefficientSupportedOpenConeDesc_stable_zero_bijective f T a N

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The actual initial cone comparison specializes to the unchanged canonical whole null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:195"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
def boundedAboveFlatCoefficientSupportedOpenGradingConeComparison (a : Under R) :
    mappingCone
      ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a) ⟶
      (boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T).obj a :=
  mappingConeDesc
    ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a)
    ((boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a)
    ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The original cone inclusion face is exactly the actual q component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:207"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero", reassoc]
theorem boundedAboveFlatCoefficientSupportedOpenGradingConeComparison_inclusion (a : Under R) :
    mappingConeInclusion
        ((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app a) ≫
        boundedAboveFlatCoefficientSupportedOpenGradingConeComparison f T a =
      (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a :=
  mappingConeInclusion_desc _ _ _

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- Every original cone cylinder point retains the same canonical whole-null time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:216"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingConeComparison_cylinder (a : Under R)
    (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    (boundedAboveFlatCoefficientSupportedOpenGradingConeComparison f T a).map n
      (ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).point n)
        (((boundedAboveFlatCoefficientSupportedFullOpenPrespectrumFunctor f T).obj a).point n)
        (((boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation
          f T).app a).map n)
        (s, x)) =
      ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s, x)
        := rfl

/-- The canonical whole-null specialization is stable in all integer degrees. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:229"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingConeComparison_isStableEquivalence (a :
  Under R) :
    IsStableEquivalence (boundedAboveFlatCoefficientSupportedOpenGradingConeComparison f T a) :=
  boundedAboveFlatCoefficientSupportedOpenConeDesc_isStableEquivalence f T a
    ((boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- The unchanged whole null supplies the actual coefficient-natural cone comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:236"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
def boundedAboveFlatCoefficientSupportedOpenGradingConeComparisonTransformation :
    mappingConeDiagram
      (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T :=
  mappingConeDescTransformation
    (boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (fun a ↦ (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)
    (fun {_ _} g ↦ (boundedAboveFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality g)

omit [QuasiSeparatedSpace Q.left] [CompactSpace T] in
/-- Each coefficient component retains precisely the original canonical cone descent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenConeStable.lean:248"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
theorem boundedAboveFlatCoefficientSupportedOpenGradingConeComparisonTransformation_app (a : Under
  R) :
    (boundedAboveFlatCoefficientSupportedOpenGradingConeComparisonTransformation f T).app a =
      boundedAboveFlatCoefficientSupportedOpenGradingConeComparison f T a := rfl

end AlgebraicGeometry.Scheme.Modules

