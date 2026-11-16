/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedCoarseNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenConeComparison
public import Colib.CategoryTheory.Waldhausen.AsSmall.Composition
public import Colib.KTheory.Waldhausen.Iterated.ExactModelEquivalence
public import Colib.Topology.Prespectrum.ConeStableNaturality
public import Colib.Topology.Prespectrum.ConeDescNaturality
/-! # Stability of the original ordinary supported coarse cone

Exact evaluation equivalences compare the actual supported inclusion and its complete original
null with the geometric acyclic inclusion. The original excision and geometric fibration prove
stability of this same cone map; no auxiliary union-support object or stable hypothesis is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Topology Topology.LoopPrespectrum HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation
  boundedAboveFlatCoefficientSupportedSectionEquivalence
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]
/-- The exact support evaluation equivalence with the native small target. -/
def supportAcyclicSmallEquivalence (a : Under R) :=
  (boundedAboveFlatCoefficientSupportAcyclicEquivalence f a).trans AsSmall.equiv

/-- Support evaluation preserves the native relative-acyclic exact structure. -/
theorem supportAcyclicSmall_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.cof
      (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.weq
      (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).asSmall.cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).asSmall.weq
      (supportAcyclicSmallEquivalence f a).functor :=
  (boundedAboveFlatCoefficientSupportAcyclicEvaluation_exact f a).comp
    (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).asSmall_up_exact

/-- Inverse support evaluation is exact in the native small category. -/
theorem supportAcyclicSmall_inverse_exact (a : Under R) :
    IsExact (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).asSmall.cof
      (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).asSmall.weq
      (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.cof
      (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.weq
      (supportAcyclicSmallEquivalence f a).inverse :=
  (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).asSmall_down_exact.comp
    (boundedAboveFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a)

/-- Evaluate supported sections into the native relative-acyclic model. -/
def supportAcyclicModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedModel f a ⟶
      asSmallCategory (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a)))  :=
  ⟨⟨(supportAcyclicSmallEquivalence f a).functor, supportAcyclicSmall_exact f a⟩,
    congrArg AsSmall.up.obj (boundedAboveFlatCoefficientSupportAcyclicEvaluation_zero f a)⟩

/-- The ambient evaluation equivalence with the native small target. -/
def ambientSmallEquivalence (a : Under R) :=
  (boundedAboveFlatCoefficientSectionEquivalence (op Q, a)).trans AsSmall.equiv

/-- Ambient evaluation is exact in the native bounded-flat model. -/
theorem ambientSmall_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).cof
      (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).weq
      (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace).asSmall.weq
      (ambientSmallEquivalence (Q := Q) a).functor :=
  (boundedAboveFlatCoefficientOriginalEvaluation_exact (op Q, a)).comp
    (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace).asSmall_up_exact

/-- Inverse ambient evaluation is exact in the native model. -/
theorem ambientSmall_inverse_exact (a : Under R) :
    IsExact (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace).asSmall.weq
      (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).cof
      (boundedAboveFlatCoefficientSectionWaldhausen (op Q, a)).weq
      (ambientSmallEquivalence (Q := Q) a).inverse :=
  (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace).asSmall_down_exact.comp
    (boundedAboveFlatCoefficientSectionEquivalence_inverse_exact (op Q, a))

/-- Evaluate the actual ambient sections at the original chosen zero. -/
def ambientEvaluationModelMap (a : Under R) :
    boundedAboveFlatCoefficientSectionModel (op Q, a) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace)  :=
  ⟨⟨(ambientSmallEquivalence (Q := Q) a).functor, ambientSmall_exact a⟩,
    congrArg AsSmall.up.obj (boundedAboveFlatCoefficientOriginalEvaluation_sectionZero (op Q, a))⟩

/-- Ambient evaluation is exact for the relative-open weak equivalences. -/
theorem openSmall_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientOpenWaldhausen f a).cof
      (boundedAboveFlatCoefficientOpenWaldhausen f a).weq
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmall.cof
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmall.weq
      (ambientSmallEquivalence (Q := Q) a).functor :=
  (boundedAboveFlatCoefficientOpenEvaluation_coarse_exact f a).comp
    (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmall_up_exact

/-- Inverse evaluation is exact for the relative-open weak equivalences. -/
theorem openSmall_inverse_exact (a : Under R) :
    IsExact (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmall.cof
      (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmall.weq
      (boundedAboveFlatCoefficientOpenWaldhausen f a).cof
      (boundedAboveFlatCoefficientOpenWaldhausen f a).weq
      (ambientSmallEquivalence (Q := Q) a).inverse :=
  (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmall_down_exact.comp
    (boundedAboveFlatCoefficientOpenEquivalence_inverse_exact f a)

/-- Evaluate the ambient sections with the relative-open weak equivalences. -/
def openEvaluationModelMap (a : Under R) :
    boundedAboveFlatCoefficientOpenModel f a ⟶
      asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a))  :=
  ⟨⟨(ambientSmallEquivalence (Q := Q) a).functor, openSmall_exact f a⟩,
    (ambientEvaluationModelMap (Q := Q) a).property⟩

/-- The support evaluation commutes with actual inclusion. -/
theorem evaluation_inclusion (a : Under R) :
    boundedAboveFlatCoefficientSupportedForgetModelMap f a ≫ ambientEvaluationModelMap a =
      supportAcyclicModelMap f a ≫
        asSmallCategoryMap _ _ (acyclicInclusion_exact
          (boundedAboveFlatPerfectOpenNested (schemeMap f a))) rfl := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact asSmallFunctor_square (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι
    (boundedAboveFlatCoefficientOriginalEvaluation (op Q, a))
    (boundedAboveFlatCoefficientSupportAcyclicEvaluation f a)
    (acyclicInclusion (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
    (boundedAboveFlatCoefficientSupportAcyclicEvaluation_inclusion f a).symm

/-- The original evaluation commutes with changing weak equivalences. -/
theorem evaluation_changeWeak (a : Under R) :
    boundedAboveFlatCoefficientOpenChangeWeakModelMap f a ≫ openEvaluationModelMap f a =
      ambientEvaluationModelMap a ≫ asSmallCategoryMap _ _
        (changeWeak_exact (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
        (boundedAboveFlatPerfectOpenNested (schemeMap f a)).zero_eq.symm := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  change 𝟭 _ ⋙ (ambientSmallEquivalence (Q := Q) a).functor =
    (ambientSmallEquivalence (Q := Q) a).functor ⋙ 𝟭 _
  rw [Functor.id_comp, Functor.comp_id]

/-- The actual evaluation maps commute with the supported inclusion. -/
def supportEvaluationSquare (a : Under R) :
    Arrow.mk ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a) ⟶
      Arrow.mk (acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f
        a))) :=
  Arrow.homMk (prespectrumMap (supportAcyclicModelMap f a))
    (prespectrumMap (ambientEvaluationModelMap a))
    ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (evaluation_inclusion f a)).trans
        (prespectrumFunctor.map_comp _ _))).symm

/-- Evaluation preserves every point of the prescribed support nullhomotopy. -/
theorem null_evaluation (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedPrespectrumFunctor f).obj a).space n) :
    (prespectrumMap (openEvaluationModelMap f a)).map n
        (((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectOpenNested (schemeMap f a))).level n
        (s, (prespectrumMap (supportAcyclicModelMap f a)).map n x) := by
  let N := boundedAboveFlatPerfectOpenNested (schemeMap f a)
  let F := boundedAboveFlatCoefficientSupportedForgetModelMap f a ≫
    boundedAboveFlatCoefficientOpenChangeWeakModelMap f a
  let G := asSmallCategoryMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  have hs : F ≫ openEvaluationModelMap f a = supportAcyclicModelMap f a ≫ G := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    apply asSmallFunctor_square F.hom.toFunctor (boundedAboveFlatCoefficientOriginalEvaluation (op
      Q, a))
      (boundedAboveFlatCoefficientSupportAcyclicEvaluation f a) (acyclicInclusion N)
    exact (congrArg (fun K ↦ K ⋙ boundedAboveFlatCoefficientOriginalEvaluation (op Q, a))
      (Functor.comp_id (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι)).trans
        (boundedAboveFlatCoefficientSupportAcyclicEvaluation_inclusion f a).symm
  let θ : (CategoryTheory.Waldhausen.IteratedS.zeroHom
      (asSmallCategory (acyclicStructure N)) (asSmallCategory N.coarse)).hom.toFunctor ⟶
        G.hom.toFunctor :=
    whiskerLeft AsSmall.down (whiskerRight (zeroToAcyclicInclusion N) AsSmall.up)
  have hθ : ∀ A, (asSmallCategory N.coarse).obj.waldhausen.weq (θ.app A) :=
    fun A ↦ zeroToAcyclicInclusion_weak N (AsSmall.down.obj A)
  have h := prespectrumZeroTransformationHomotopy_naturality F G (supportAcyclicModelMap f a)
    (openEvaluationModelMap f a) hs (boundedAboveFlatCoefficientSupportedZeroToOpen f a) θ
    (boundedAboveFlatCoefficientSupportedZeroToOpen_weak f a) hθ n
  exact congrArg (fun H ↦ H (unitInterval.symm s, x)) h

/-- The literal support evaluation map is invertible in every signed stable degree. -/
theorem supportAcyclicModelMap_isStableEquivalence (a : Under R) :
    IsStableEquivalence (prespectrumMap (supportAcyclicModelMap f a)) :=
  ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatCoefficientSupportedModel f a)
    (W := asSmallCategory (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))))
    (supportAcyclicSmallEquivalence f a) (supportAcyclicSmall_exact f a)
    (supportAcyclicSmall_inverse_exact f a) (supportAcyclicModelMap f a).property

/-- Genuine geometric fibration proves stability of the exact original native support cone. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportLocalizationModels.lean:415"
  "adaptation" "Original geometric fibration and exact evaluation prove ordinary cone stability"]
theorem boundedAboveFlatCoefficientSupportedOpenConeComparison_isStableEquivalence (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedOpenConeComparison f).app a) := by
  have he : mappingConeMap (supportEvaluationSquare f a) ≫
      boundedAboveFlatPerfectOpenConeComparison (schemeMap f a) =
    (boundedAboveFlatCoefficientSupportedOpenConeComparison f).app a ≫
      prespectrumMap (openEvaluationModelMap f a) :=
    mappingConeDesc_naturality (supportEvaluationSquare f a)
      ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
      (changeWeakPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
      (prespectrumMap (openEvaluationModelMap f a))
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
      (acyclicPrespectrumNullhomotopy (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
      ((prespectrumFunctor.map_comp _ _).symm.trans
        ((congrArg prespectrumFunctor.map (evaluation_changeWeak f a)).trans
          (prespectrumFunctor.map_comp _ _))).symm (null_evaluation f a)
  have hs := supportAcyclicModelMap_isStableEquivalence f a
  have ha := ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatCoefficientSectionModel (op Q, a))
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (space (op Q, a)).toRingedSpace))
    (ambientSmallEquivalence (Q := Q) a) (ambientSmall_exact a)
    (ambientSmall_inverse_exact a) (ambientEvaluationModelMap (Q := Q) a).property
  have hc := (mappingConeMap_isStableEquivalence_of_excision (supportEvaluationSquare f a)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _)
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _) hs ha).comp
      (boundedAboveFlatPerfectOpenConeComparison_isStableEquivalence (schemeMap f a))
  rw [he] at hc
  have ho := ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatCoefficientOpenModel f a)
    (W := asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)))
    (ambientSmallEquivalence (Q := Q) a) (openSmall_exact f a) (openSmall_inverse_exact f a)
    (openEvaluationModelMap f a).property
  intro d
  let : IsIso ((stableHomotopyFunctor d).map (prespectrumMap (openEvaluationModelMap f a))) :=
    ho d
  have hd := hc d
  rw [Functor.map_comp] at hd
  exact (isIso_comp_right_iff _ _).mp hd

end AlgebraicGeometry.Scheme.Modules
