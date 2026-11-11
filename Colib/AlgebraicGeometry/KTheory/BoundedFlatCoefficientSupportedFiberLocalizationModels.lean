/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientFiberInclusion
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedEvaluationJoint
public import Colib.KTheory.Waldhausen.Iterated.DiagramZeroNull
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.JointRetarget
public import Colib.CategoryTheory.ObjectProperty.LiftInclusion
public import Colib.CategoryTheory.Waldhausen.AsSmall.Composition
public import Colib.KTheory.Waldhausen.Iterated.ExactModelEquivalence
public import Colib.KTheory.Waldhausen.Fibration.ConeComparison
public import Colib.Topology.Prespectrum.ConeStableNaturality
public import Colib.Topology.Prespectrum.ConeDescNaturality
public import Colib.Topology.Prespectrum.ConeDiagramDescent
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenFibration

/-!
# Original auxiliary-supported native fiber, ambient and coarse cone

The actual native intersection support is vanishing on the union of the
original auxiliary open and original localization open. Its literal inclusion
into auxiliary support, the unchanged coarse weakness and their joint zero
construct the same coefficient-natural reversed zero-to-inclusion whole null.

Actual supported joint cylinders transport through genuine ordinary exact
evaluation. The transported second endpoint, original weak predicate and
extension with the genuine image zero prove the native fibration theorem.
Literal native acyclic conversion and AsSmall.up then retain the actual chosen
joint zero and every canonical null time in the original cone comparison.

No independently chosen geometric zeros are identified. The initial cone
result requires no compactness or separation and asserts no seed, telescope
or classical nonconnective K-theory comparison.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.Fibration CategoryTheory.Waldhausen.IteratedS
open Topology CategoryTheory.Waldhausen.SmallWaldhausenCategory
open Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.RingedSpace
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation
    boundedAboveFlatCoefficientSupportedSectionEquivalence

/-- The identity coefficient reindexing square forgets only the extra support open. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:58"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberForget_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.cof
      (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.weq
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.cof
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.weq
      (boundedAboveFlatCoefficientSupportedFiberForget f T a) := by
  let l := (space (op Q, a)).homOfLE
    (show boundedAboveFlatCoefficientSupportOpen Q T a ≤
      boundedAboveFlatCoefficientFiberSupportOpen f T a
      from le_sup_left)
  have h : l ≫ (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι =
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι ≫
        AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (𝟙 (op Q, a)) := by
    rw [AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id, Category.comp_id]
    exact Scheme.homOfLE_ι _ _
  have hM : boundedAboveFlatCoefficientSupportedSectionsMap
      (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι (𝟙 (op Q, a)) l h =
      boundedAboveFlatCoefficientSupportedFiberForget f T a := by
    change (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q
      T a).ι).lift
      ((boundedAboveFlatCoefficientSectionSupported
        (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).ι ⋙
        boundedAboveFlatCoefficientSectionsMap (𝟙 (op Q, a))) _ =
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
        a).ι).lift
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen
          f T a).ι).ι
          _
    apply supportLift_congr
    exact (congrArg (fun F ↦ (boundedAboveFlatCoefficientSectionSupported
      (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).ι ⋙ F)
      (CategoryTheory.StrictSections.underCocartesianReindex_id
        (boundedAboveFlatCoefficientProjection R) (op Q, a))).trans (Functor.comp_id _)
  rw [← hM]
  exact boundedAboveFlatCoefficientSupportedSectionsMap_exact
    (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι (𝟙 (op Q, a)) l h

/-- The literal support inclusion retains the original restricted joint zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:94"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberForgetModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedFiberModel f T a ⟶
      boundedAboveFlatCoefficientSupportedAmbientModel T a :=
  ⟨⟨boundedAboveFlatCoefficientSupportedFiberForget f T a,
    boundedAboveFlatCoefficientSupportedFiberForget_exact f T a⟩, rfl⟩

/-- Every original coefficient map preserves the same intersection-support inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:102"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation :
    boundedAboveFlatCoefficientSupportedFiberModelFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedAmbientModelFunctor T where
  app := boundedAboveFlatCoefficientSupportedFiberForgetModelMap f T
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    rfl

/-- Original native fine ambient prespectra retaining auxiliary closed support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:111"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor

/-- Original native fine prespectra on the actual intersection of the closed supports. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:116"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  boundedAboveFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor

/-- Original realization of the actual intersection-support inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:121"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation :
    boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T :=
  Functor.whiskerRight (boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T)
    prespectrumFunctor

/-- Original supported ambient identity change to the relative-open coarse weakness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:128"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation :
    boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T ⟶
      boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T :=
  Functor.whiskerRight (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T)
    prespectrumFunctor

/-- The unique original zero-to-intersection-support inclusion transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:135"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberZeroToOpen (a : Under R) :
    (Functor.const (BoundedAboveFlatCoefficientSupportedFiberSections f T a)).obj
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.zero ⟶
        boundedAboveFlatCoefficientSupportedFiberForget f T a where
  app S := (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.isZero.to_
    ((boundedAboveFlatCoefficientSupportedFiberForget f T a).obj S)
  naturality _ _ _ :=
    (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.isZero.eq_of_src _ _

/-- Actual intersection support makes this same zero-to-inclusion transformation coarse weak. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:145"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberZeroToOpen_weak (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedFiberSections f T a) :
    (boundedAboveFlatCoefficientSupportedOpenModel f T a).obj.waldhausen.weq
      ((boundedAboveFlatCoefficientSupportedFiberZeroToOpen f T a).app S) := by
  change (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a).weq _
  apply (boundedAboveFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a _).mpr
  let N := boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a)
  let K := (boundedAboveFlatCoefficientSupportedEvaluation
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).obj
      ((boundedAboveFlatCoefficientSupportedFiberForget f T a).obj S)
  have hK : Acyclic N.coarse K := by
    apply (boundedAboveFlatPerfectSupportedOpenAcyclic_iff (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a) K).mpr
    dsimp only [K]
    rw [boundedAboveFlatCoefficientSupportedEvaluation_obj]
    exact (boundedAboveFlatCoefficientFiberSupported_iff f T a
      ((boundedAboveFlatCoefficientSupportedFiberForget f T a).obj S)).mp S.property
  have hZ : IsZero ((boundedAboveFlatCoefficientSupportedEvaluation
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι).obj
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.zero) :=
    boundedAboveFlatCoefficientSupportedEvaluation_sectionZero_isZero _
  have hp : (boundedAboveFlatCoefficientSupportedEvaluation
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι).map
      ((boundedAboveFlatCoefficientSupportedFiberZeroToOpen f T a).app S) = hZ.to_ K :=
    hZ.eq_of_src _ _
  rw [hp]
  exact (acyclic_iff_weak_from_isZero N.coarse hZ K).mp hK

/-- Reverse the original weak zero-to-inclusion realization with every time retained. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:175"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation
      f T)
      (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T) :=
  modelDiagramZeroNull (boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T)
    (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T)
    (boundedAboveFlatCoefficientSupportedFiberZeroToOpen f T)
    (boundedAboveFlatCoefficientSupportedFiberZeroToOpen_weak f T)

/-- The original native intersection-support cone descends along the same complete null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:184"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberOpenConeComparison :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f
      T) ⟶
      boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T :=
  mappingConeDescTransformation
    (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation
    f T) (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).naturality

/-- The original ambient cone face is precisely the actual supported change of weakness. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:194"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberOpenConeComparison_inclusion (a : Under R) :
    mappingConeInclusion
      ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a) ≫
      (boundedAboveFlatCoefficientSupportedFiberOpenConeComparison f T).app a =
      (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a :=
  mappingConeInclusion_desc _ _ _

/-- Each original cone cylinder retains the actual canonical support-null time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:202"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberOpenConeComparison_cylinder
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedFiberOpenConeComparison f T).app a).map m
      (Topology.ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app
          a).map m)
        (s, x)) =
      ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level m (s, x)
        := rfl

private theorem twoOutOfThree_of_evaluation {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (F : C ⥤ D)
    [W.weq.HasTwoOutOfThreeProperty]
    (hw : ∀ {X Y} (p : X ⟶ Y), V.weq p ↔ W.weq (F.map p)) :
    V.weq.HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := by
    apply (hw _).mpr
    rw [F.map_comp]
    exact W.weq.comp_mem _ _ ((hw _).mp hf) ((hw _).mp hg)
  of_postcomp f g hg hfg := by
    apply (hw _).mpr
    apply W.weq.of_postcomp (W' := W.weq) _ (F.map g) ((hw _).mp hg)
    simpa only [F.map_comp] using (hw _).mp hfg
  of_precomp f g hf hfg := by
    apply (hw _).mpr
    apply W.weq.of_precomp (W' := W.weq) (F.map f) _ ((hw _).mp hf)
    simpa only [F.map_comp] using (hw _).mp hfg

private theorem extension_of_evaluation {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (F : C ⥤ D)
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hw : ∀ {X Y} (p : X ⟶ Y), V.weq p ↔ W.weq (F.map p))
    (he : ExtensionAxiom W) : ExtensionAxiom V where
  extension hi hi' h h' a b c wi wq ha hc := by
    apply (hw _).mpr
    let hZ := hF.zero V.isZero
    have mapped {X Y S : C} {j : X ⟶ Y} {r : Y ⟶ S}
        (hj : V.cof j) (hp : IsPushout j (V.isZero.from_ X) r (V.isZero.to_ S)) :
        IsPushout (F.map j) (hZ.from_ (F.obj X)) (F.map r) (hZ.to_ (F.obj S)) := by
      convert! hF.pushout hj hp using 1
      · exact hZ.eq_of_tgt _ _
      · exact hZ.eq_of_src _ _
    exact he.extension_of_isZero hZ (hF.cofibration _ hi) (hF.cofibration _ hi')
      (mapped hi h) (mapped hi' h') (F.map a) (F.map b) (F.map c)
      (by simpa only [F.map_comp] using congrArg F.map wi)
      (by simpa only [F.map_comp] using congrArg F.map wq)
      ((hw _).mp ha) ((hw _).mp hc)

private theorem equivalenceJoint_secondEndpoint {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (e : C ≌ D)
    (hF : IsExact V.cof V.weq W.cof W.weq e.functor)
    (hG : IsExact W.cof W.weq V.cof V.weq e.inverse)
    (J : RowFactorization.JointData (NestedWeakEquivalences.refl V))
    (hJ : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl V) J) :
    RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W)
      (RowFactorization.JointData.ofExactEquivalence V W e hF hG J) := by
  intro f
  change ((e.counitIso.app f.right).inv ≫ e.functor.map (J.inr.app (e.inverse.mapArrow.obj f))) ≫
    e.functor.map (J.joint.obj (e.inverse.mapArrow.obj f)).obj.hom ≫
    (e.functor.map (J.projection.app (e.inverse.mapArrow.obj f)) ≫ (e.counitIso.app f.right).hom) =
      𝟙 _
  have ht := congrArg e.functor.map (hJ (e.inverse.mapArrow.obj f))
  simp only [Functor.map_comp] at ht
  calc
    _ = (e.counitIso.app f.right).inv ≫
        (e.functor.map (J.inr.app (e.inverse.mapArrow.obj f)) ≫
          e.functor.map (J.joint.obj (e.inverse.mapArrow.obj f)).obj.hom ≫
          e.functor.map (J.projection.app (e.inverse.mapArrow.obj f))) ≫ (e.counitIso.app
            f.right).hom := by
            simp only [Category.assoc]
    _ = 𝟙 _ := by rw [ht]; simp

private def supportedNativeJointData (a : Under R) :
    RowFactorization.JointData (boundedAboveFlatCoefficientSupportedOpenNested f T a) :=
  (boundedAboveFlatCoefficientSupportedSectionJointData
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι).toNested
    (boundedAboveFlatCoefficientSupportedOpenNested f T a)

private theorem supportedSectionJoint_secondEndpoint {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] :
    RowFactorization.SecondEndpointSection
      (NestedWeakEquivalences.refl (boundedAboveFlatCoefficientSupportedSectionWaldhausen j))
      (boundedAboveFlatCoefficientSupportedSectionJointData j) :=
  equivalenceJoint_secondEndpoint
    (boundedAboveFlatPerfectSupportedWaldhausen j)
    (boundedAboveFlatCoefficientSupportedSectionWaldhausen
      j)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence
      j).symm
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact
      j)
    (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact
      j)
    (boundedAboveFlatPerfectSupportedJointData j)
    (complexJointDataOfNested_secondEndpointSection
      (boundedAboveFlatPerfectSupported j)
      (fun hK hL p ↦ boundedAboveFlatPerfectSupported_mappingCone
        j hK hL p)
      (fun _ hK ↦ boundedAboveFlatPerfectSupported_shift_one j hK) _)

private theorem secondEndpoint_toNested {C : Type*} [Category* C] {V : Structure C}
    (J : RowFactorization.JointData (NestedWeakEquivalences.refl V))
    (N : NestedWeakEquivalences V)
    (hJ : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl V) J) :
    RowFactorization.SecondEndpointSection N (J.toNested N) := hJ

omit [IsOpenImmersion f.left] in
private theorem supportedNativeJoint_secondEndpoint (a : Under R) :
    RowFactorization.SecondEndpointSection (boundedAboveFlatCoefficientSupportedOpenNested f T a)
      (supportedNativeJointData f T a) :=
  secondEndpoint_toNested (boundedAboveFlatCoefficientSupportedSectionJointData
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι)
      (boundedAboveFlatCoefficientSupportedOpenNested f T a)
    (supportedSectionJoint_secondEndpoint (boundedAboveFlatCoefficientSupportOpen Q T a).ι)

private theorem supportedNative_canonicalCone_isStableEquivalence (a : Under R) :
    IsStableEquivalence
      (canonicalConePrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a)) := by
  let N := boundedAboveFlatCoefficientSupportedOpenNested f T a
  let W := boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a)
  let E := boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientSupportOpen
    Q T a).ι
  have hw : ∀ {X Y} (p : X ⟶ Y), N.coarse.weq p ↔ W.weq (E.map p) :=
    fun p ↦ boundedAboveFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a p
  let : W.weq.HasTwoOutOfThreeProperty :=
    boundedAboveFlatPerfectSupportedOpenNested_twoOutOfThree (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)
  let : N.coarse.weq.HasTwoOutOfThreeProperty :=
    twoOutOfThree_of_evaluation N.coarse W E hw
  have he : ExtensionAxiom N.coarse :=
    extension_of_evaluation N.coarse W E
      (boundedAboveFlatCoefficientSupportedOpenEvaluation_coarse_exact f T a) hw
      (boundedAboveFlatPerfectSupportedOpenWaldhausen_extensionAxiom (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a))
  exact canonicalConePrespectrumMap_isStableEquivalence_general N he
    (supportedNativeJointData f T a) (supportedNativeJoint_secondEndpoint f T a)

private theorem acyclic_evaluation_iff {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) (W : Structure D) (F : C ⥤ D)
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hw : ∀ {X Y} (p : X ⟶ Y), V.weq p ↔ W.weq (F.map p)) (X : C) :
    Acyclic V X ↔ Acyclic W (F.obj X) := by
  let hZ := hF.zero V.isZero
  have hp : F.map (V.isZero.to_ X) = hZ.to_ (F.obj X) := hZ.eq_of_src _ _
  change V.weq (V.isZero.to_ X) ↔ Acyclic W (F.obj X)
  rw [hw, hp]
  exact (acyclic_iff_weak_from_isZero W hZ _).symm

private theorem supportedNativeAcyclic_evaluation_iff (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    Acyclic (boundedAboveFlatCoefficientSupportedOpenNested f T a).coarse S ↔
      Acyclic (boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)).coarse
        ((boundedAboveFlatCoefficientSupportedEvaluation
          (boundedAboveFlatCoefficientSupportOpen Q T a).ι).obj S) :=
  acyclic_evaluation_iff (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a)
    (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a))
    (boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientSupportOpen Q T
      a).ι)
    (boundedAboveFlatCoefficientSupportedOpenEvaluation_coarse_exact f T a)
    (fun p ↦ boundedAboveFlatCoefficientSupportedOpenWaldhausen_weq_iff f T a p) S

/-- Original native coarse acyclicity is precisely the true intersection-support condition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:371"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedOpenAcyclic_iff (a : Under R)
    (S : BoundedAboveFlatCoefficientSupportedAmbientSections (Q := Q) T a) :
    Acyclic (boundedAboveFlatCoefficientSupportedOpenNested f T a).coarse S ↔
      boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f T
        a).ι
        S.obj := by
  rw [supportedNativeAcyclic_evaluation_iff]
  change Acyclic (boundedAboveFlatPerfectSupportedOpenWaldhausen (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a))
    ((boundedAboveFlatCoefficientSupportedEvaluation
      (boundedAboveFlatCoefficientSupportOpen Q T a).ι).obj S) ↔ _
  rw [boundedAboveFlatPerfectSupportedOpenAcyclic_iff,
    boundedAboveFlatCoefficientSupportedEvaluation_obj]
  exact (boundedAboveFlatCoefficientFiberSupported_iff f T a S).symm

/-- The actual intersection support is exactly acyclicity inside the original native support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:385"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberToAcyclic (a : Under R) :
    BoundedAboveFlatCoefficientSupportedFiberSections f T a ⥤
      AcyclicCategory (boundedAboveFlatCoefficientSupportedOpenNested f T a) where
  obj S := ⟨(boundedAboveFlatCoefficientSupportedFiberForget f T a).obj S,
    (boundedAboveFlatCoefficientSupportedOpenAcyclic_iff f T a _).mpr S.property⟩
  map p := ObjectProperty.homMk ((boundedAboveFlatCoefficientSupportedFiberForget f T a).map p)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Flatten original native acyclic sections to the actual intersection-support section. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:395"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedAcyclicToFiber (a : Under R) :
    AcyclicCategory (boundedAboveFlatCoefficientSupportedOpenNested f T a) ⥤
      BoundedAboveFlatCoefficientSupportedFiberSections f T a where
  obj S := ⟨S.obj.obj, (boundedAboveFlatCoefficientSupportedOpenAcyclic_iff f T a S.obj).mp
    S.property⟩
  map p := ObjectProperty.homMk p.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The native support comparison is a genuine literal flattening equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:404"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
def boundedAboveFlatCoefficientSupportedFiberAcyclicEquivalence (a : Under R) :
    BoundedAboveFlatCoefficientSupportedFiberSections f T a ≌
      AcyclicCategory (boundedAboveFlatCoefficientSupportedOpenNested f T a) :=
  CategoryTheory.Equivalence.mk
    (boundedAboveFlatCoefficientSupportedFiberToAcyclic f T a)
    (boundedAboveFlatCoefficientSupportedAcyclicToFiber f T a)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl))

/-- The same fine support-forget map is retained literally by native acyclic conversion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:416"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberToAcyclic_inclusion (a : Under R) :
    boundedAboveFlatCoefficientSupportedFiberToAcyclic f T a ⋙
      acyclicInclusion (boundedAboveFlatCoefficientSupportedOpenNested f T a) =
      boundedAboveFlatCoefficientSupportedFiberForget f T a := rfl

private theorem acyclic_lift_exact {C D : Type*} [Category* C] [Category* D]
    (V : Structure C) {W : Structure D} (N : NestedWeakEquivalences W)
    (F : C ⥤ AcyclicCategory N)
    (h : IsExact V.cof V.weq W.cof W.weq (F ⋙ acyclicInclusion N)) :
    IsExact V.cof V.weq (acyclicStructure N).cof (acyclicStructure N).weq F where
  zero hZ := IsZero.of_full_of_faithful_of_isZero (acyclicObjects N).ι _ (h.zero hZ)
  cofibration p hp := h.cofibration p hp
  weak p hp := h.weak p hp
  pushout hi hp := IsPushout.of_map_of_faithful (acyclicObjects N).ι (h.pushout hi hp)

private theorem supportedNativeFiberToAcyclic_exact (a : Under R) :
    IsExact (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.cof
      (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.weq
      (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedAboveFlatCoefficientSupportedFiberToAcyclic f T a) :=
  acyclic_lift_exact (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen
    (boundedAboveFlatCoefficientSupportedOpenNested f T a)
    (boundedAboveFlatCoefficientSupportedFiberToAcyclic f T a)
    ((boundedAboveFlatCoefficientSupportedFiberToAcyclic_inclusion f T a).symm ▸
      boundedAboveFlatCoefficientSupportedFiberForget_exact f T a)

private def supportedNativeAcyclicEvaluation (a : Under R) :
    AcyclicCategory (boundedAboveFlatCoefficientSupportedOpenNested f T a) ⥤
      AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)) :=
  (acyclicObjects (boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
    (boundedAboveFlatCoefficientSupportOpen Q T a))).lift
    (acyclicInclusion (boundedAboveFlatCoefficientSupportedOpenNested f T a) ⋙
      boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientSupportOpen Q T
        a).ι)
    (fun S ↦ (supportedNativeAcyclic_evaluation_iff f T a S.obj).mp S.property)

private theorem supportedNativeAcyclicEvaluation_inclusion (a : Under R) :
    supportedNativeAcyclicEvaluation f T a ⋙
      acyclicInclusion (boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a)) =
      acyclicInclusion (boundedAboveFlatCoefficientSupportedOpenNested f T a) ⋙
        boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientSupportOpen Q T
          a).ι :=
  CategoryTheory.ObjectProperty.lift_comp_ι _ _ _

private theorem supportedNativeAcyclicEvaluation_exact (a : Under R) :
    IsExact (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).weq
      (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a))).cof
      (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a))).weq
      (supportedNativeAcyclicEvaluation f T a) :=
  acyclic_lift_exact (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a))
    (boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)) (supportedNativeAcyclicEvaluation f T a)
    ((supportedNativeAcyclicEvaluation_inclusion f T a).symm ▸
      (acyclicInclusion_exact (boundedAboveFlatCoefficientSupportedOpenNested f T a)).comp
        (boundedAboveFlatCoefficientSupportedEvaluation_exact
          (boundedAboveFlatCoefficientSupportOpen Q T a).ι))

private theorem nestedEvaluation_flatten {C D : Type*} [Category* C] [Category* D]
    (P Q : ObjectProperty C) (R : ObjectProperty P.FullSubcategory)
    (A B : ObjectProperty D) (S : ObjectProperty A.FullSubcategory) (E : C ⥤ D)
    (hQ : ∀ X : R.FullSubcategory, Q X.obj.obj)
    (hA : ∀ X : P.FullSubcategory, A (E.obj X.obj))
    (hB : ∀ X : S.FullSubcategory, B X.obj.obj)
    (hBE : ∀ X : Q.FullSubcategory, B (E.obj X.obj))
    (hS : ∀ X : R.FullSubcategory, S ((A.lift (P.ι ⋙ E) hA).obj X.obj)) :
    ({ obj := fun X ↦ ⟨X.obj.obj, hQ X⟩
       map := fun p ↦ ObjectProperty.homMk p.hom.hom
       map_id := fun _ ↦ rfl
       map_comp := fun _ _ ↦ rfl } : R.FullSubcategory ⥤ Q.FullSubcategory) ⋙
      B.lift (Q.ι ⋙ E) hBE =
      S.lift (R.ι ⋙ A.lift (P.ι ⋙ E) hA) hS ⋙
      ({ obj := fun X ↦ ⟨X.obj.obj, hB X⟩
         map := fun p ↦ ObjectProperty.homMk p.hom.hom
         map_id := fun _ ↦ rfl
         map_comp := fun _ _ ↦ rfl } : S.FullSubcategory ⥤ B.FullSubcategory) := rfl

private theorem supportedNativeAcyclicToFiber_evaluation (a : Under R) :
    boundedAboveFlatCoefficientSupportedAcyclicToFiber f T a ⋙
      boundedAboveFlatCoefficientSupportedEvaluation
      (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι =
      supportedNativeAcyclicEvaluation f T a ⋙
        boundedAboveFlatPerfectSupportedOpenAcyclicToSupported
        (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a) := by
  unfold boundedAboveFlatCoefficientSupportedAcyclicToFiber supportedNativeAcyclicEvaluation
    boundedAboveFlatPerfectSupportedOpenAcyclicToSupported
  unfold boundedAboveFlatCoefficientSupportedEvaluation acyclicInclusion
  exact nestedEvaluation_flatten
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T a).ι)
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f T
      a).ι)
    (acyclicObjects (boundedAboveFlatCoefficientSupportedOpenNested f T a))
    (boundedAboveFlatPerfectSupported (boundedAboveFlatCoefficientSupportOpen Q T a).ι)
    (boundedAboveFlatPerfectSupported (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι)
    (acyclicObjects (boundedAboveFlatPerfectSupportedOpenNested (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a)))
    (boundedAboveFlatCoefficientOriginalEvaluation (op Q, a) ⋙
      (boundedAboveFlatPerfectComplex (space (op Q, a)).toRingedSpace).ι)
    (fun X ↦ (boundedAboveFlatCoefficientSupportedOpenAcyclic_iff f T a X.obj).mp X.property)
    (fun X ↦ ⟨((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj X.obj).property,
      X.property⟩)
    (fun X ↦ (boundedAboveFlatPerfectSupported_sup_opensRange_iff (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a) X.obj.obj).mpr
      ⟨X.obj.property, (boundedAboveFlatPerfectSupportedOpenAcyclic_iff (schemeMap f a)
        (boundedAboveFlatCoefficientSupportOpen Q T a) X.obj).mp X.property⟩)
    (fun X ↦ ⟨((boundedAboveFlatCoefficientOriginalEvaluation (op Q, a)).obj X.obj).property,
      X.property⟩)
    (fun X ↦ by
      have h := (supportedNativeAcyclic_evaluation_iff f T a X.obj).mp X.property
      unfold boundedAboveFlatCoefficientSupportedEvaluation at h
      exact h)

private theorem supportedNativeAcyclicToFiber_evaluation_exact (a : Under R) :
    IsExact (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedAboveFlatPerfectSupportedWaldhausen
        (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen
        (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).weq
      (boundedAboveFlatCoefficientSupportedAcyclicToFiber f T a ⋙
        boundedAboveFlatCoefficientSupportedEvaluation
        (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι) := by
  rw [supportedNativeAcyclicToFiber_evaluation]
  exact (supportedNativeAcyclicEvaluation_exact f T a).comp
    (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_exact (schemeMap f a)
      (boundedAboveFlatCoefficientSupportOpen Q T a))

private theorem supportedEvaluation_reflects_exact {i : Index R} {U : Scheme.{u}}
    (j : U ⟶ space i) [IsOpenImmersion j] {C : Type*} [Category* C]
    (V : Structure C) (I : C ⥤ BoundedAboveFlatCoefficientSupportedSections j)
    (h : IsExact V.cof V.weq (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (I ⋙ boundedAboveFlatCoefficientSupportedEvaluation j)) :
    IsExact V.cof V.weq (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq I := by
  let := boundedAboveFlatCoefficientSupportedEvaluation_isEquivalence j
  exact {
    zero := fun hZ ↦ IsZero.of_full_of_faithful_of_isZero
      (boundedAboveFlatCoefficientSupportedEvaluation j) _ (h.zero hZ)
    cofibration := fun p hp ↦
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen_cof_iff j _).mpr (h.cofibration p hp)
    weak := fun p hp ↦
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen_weq_iff j _).mpr (h.weak p hp)
    pushout := fun hi hp ↦ IsPushout.of_map_of_faithful
      (boundedAboveFlatCoefficientSupportedEvaluation j) (h.pushout hi hp) }

private theorem supportedNativeAcyclicToFiber_exact (a : Under R) :
    IsExact (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).cof
      (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).weq
      (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.cof
      (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.weq
      (boundedAboveFlatCoefficientSupportedAcyclicToFiber f T a) :=
  supportedEvaluation_reflects_exact (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι
    (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a))
    (boundedAboveFlatCoefficientSupportedAcyclicToFiber f T a)
    (supportedNativeAcyclicToFiber_evaluation_exact f T a)

private def supportedNativeFiberAcyclicSmallEquivalence (a : Under R) :=
  (boundedAboveFlatCoefficientSupportedFiberAcyclicEquivalence f T a).trans AsSmall.equiv.{u+1,
    u+1, 0}

private def supportedNativeFiberAcyclicModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedFiberModel f T a ⟶
      asSmallCategory (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)) :=
  ⟨⟨(supportedNativeFiberAcyclicSmallEquivalence f T a).functor,
    (supportedNativeFiberToAcyclic_exact f T a).comp
    (acyclicStructure (boundedAboveFlatCoefficientSupportedOpenNested f T a)).asSmall_up_exact⟩,
      rfl⟩

private def supportedNativeAmbientModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedAmbientModel T a ⟶
      asSmallCategory (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen :=
  ⟨⟨AsSmall.up.{u+1, u+1, 0}, (boundedAboveFlatCoefficientSupportedAmbientModel T
    a).obj.waldhausen.asSmall_up_exact⟩, rfl⟩

private def supportedNativeCoarseModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedOpenModel f T a ⟶
      asSmallCategory (boundedAboveFlatCoefficientSupportedOpenModel f T a).obj.waldhausen :=
  ⟨⟨AsSmall.up.{u+1, u+1, 0}, (boundedAboveFlatCoefficientSupportedOpenModel f T
    a).obj.waldhausen.asSmall_up_exact⟩, rfl⟩

private theorem supportedNativeEvaluation_inclusion (a : Under R) :
    boundedAboveFlatCoefficientSupportedFiberForgetModelMap f T a ≫
      supportedNativeAmbientModelMap T a =
    supportedNativeFiberAcyclicModelMap f T a ≫ asSmallCategoryMap _ _
      (acyclicInclusion_exact (boundedAboveFlatCoefficientSupportedOpenNested f T a)) rfl := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

omit [IsOpenImmersion f.left] in
private theorem supportedNativeEvaluation_changeWeak (a : Under R) :
    boundedAboveFlatCoefficientSupportedOpenChangeWeakModelMap f T a ≫
      supportedNativeCoarseModelMap f T a =
    supportedNativeAmbientModelMap T a ≫ asSmallCategoryMap _ _
      (changeWeak_exact (boundedAboveFlatCoefficientSupportedOpenNested f T a))
      (boundedAboveFlatCoefficientSupportedOpenNested f T a).zero_eq.symm := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

private def supportedNativeFiberEvaluationSquare (a : Under R) :
    Arrow.mk ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app
      a) ⟶
      Arrow.mk (acyclicInclusionPrespectrumMap
        (boundedAboveFlatCoefficientSupportedOpenNested f T a)) :=
  Arrow.homMk (prespectrumMap (supportedNativeFiberAcyclicModelMap f T a))
    (prespectrumMap (supportedNativeAmbientModelMap T a))
    ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (supportedNativeEvaluation_inclusion f T a)).trans
        (prespectrumFunctor.map_comp _ _))).symm

private theorem nativeAcyclicNull_square {C : Type u} [Category.{u} C]
    {V : Structure C} (N : NestedWeakEquivalences V) {W : WideSubcategory preservesZero.{u}}
    (F : W ⟶ (⟨{ Obj := C, waldhausen := N.coarse }⟩ : WideSubcategory preservesZero.{u}))
    (a : W ⟶ asSmallCategory (acyclicStructure N))
    (c : (⟨{ Obj := C, waldhausen := N.coarse }⟩ : WideSubcategory preservesZero.{u}) ⟶
      asSmallCategory N.coarse)
    (hs : F ≫ c = a ≫ asSmallCategoryMap (acyclicStructure N) N.coarse
      (acyclicInclusion_coarse_exact N)
      (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm))
    (η : (CategoryTheory.Waldhausen.IteratedS.zeroHom W
      (⟨{ Obj := C, waldhausen := N.coarse }⟩ : WideSubcategory preservesZero.{u})).hom.toFunctor
        ⟶ F.hom.toFunctor)
    (hη : ∀ X, N.coarse.weq (η.app X))
    (n : ℕ) (s : unitInterval) (x : (prespectrum W).space n) :
    (prespectrumMap c).map n
      ((prespectrumTransformationHomotopy η hη).level n (unitInterval.symm s, x)) =
      (acyclicPrespectrumNullhomotopy N).level n
        (s, (prespectrumMap a).map n x) := by
  let G := asSmallCategoryMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  let θ : (CategoryTheory.Waldhausen.IteratedS.zeroHom
      (asSmallCategory (acyclicStructure N)) (asSmallCategory N.coarse)).hom.toFunctor ⟶
        G.hom.toFunctor :=
    whiskerLeft AsSmall.down.{u, u, 0}
      (whiskerRight (zeroToAcyclicInclusion N) AsSmall.up.{u, u, 0})
  have hθ : ∀ A, (asSmallCategory N.coarse).obj.waldhausen.weq (θ.app A) :=
    fun A ↦ zeroToAcyclicInclusion_weak N (AsSmall.down.{u, u, 0}.obj A)
  have h := prespectrumZeroTransformationHomotopy_naturality F G a c hs η θ hη hθ n
  exact congrArg (fun H ↦ H (unitInterval.symm s, x)) h

private theorem supportedNativeFiberNull_evaluation (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space n) :
    (prespectrumMap (supportedNativeCoarseModelMap f T a)).map n
      (((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level n (s, x)) =
    (acyclicPrespectrumNullhomotopy (boundedAboveFlatCoefficientSupportedOpenNested f T a)).level n
      (s, (prespectrumMap (supportedNativeFiberAcyclicModelMap f T a)).map n x) := by
  let N := boundedAboveFlatCoefficientSupportedOpenNested f T a
  let F := boundedAboveFlatCoefficientSupportedFiberForgetModelMap f T a ≫
    boundedAboveFlatCoefficientSupportedOpenChangeWeakModelMap f T a
  let G := asSmallCategoryMap (acyclicStructure N) N.coarse (acyclicInclusion_coarse_exact N)
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm)
  have hs : F ≫ supportedNativeCoarseModelMap f T a =
      supportedNativeFiberAcyclicModelMap f T a ≫ G := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    rfl
  exact nativeAcyclicNull_square N F (supportedNativeFiberAcyclicModelMap f T a)
    (supportedNativeCoarseModelMap f T a) hs
    (boundedAboveFlatCoefficientSupportedFiberZeroToOpen f T a)
    (boundedAboveFlatCoefficientSupportedFiberZeroToOpen_weak f T a) n s x

/-- The actual native supported fibration proves the same original intersection-support cone
stable in every integer degree, without comparing independently chosen geometric zeros. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberLocalizationModels.lean:677"
  "adaptation"
    "Original union-support inclusion, selected whole null and actual coarse cone stability"]
theorem boundedAboveFlatCoefficientSupportedFiberOpenConeComparison_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedFiberOpenConeComparison f T).app a)
      := by
  let N := boundedAboveFlatCoefficientSupportedOpenNested f T a
  have he : mappingConeMap (supportedNativeFiberEvaluationSquare f T a) ≫
      canonicalConePrespectrumMap N =
    (boundedAboveFlatCoefficientSupportedFiberOpenConeComparison f T).app a ≫
      prespectrumMap (supportedNativeCoarseModelMap f T a) :=
    mappingConeDesc_naturality (supportedNativeFiberEvaluationSquare f T a)
      ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
      (changeWeakPrespectrumMap N) (prespectrumMap (supportedNativeCoarseModelMap f T a))
      ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
      (acyclicPrespectrumNullhomotopy N)
      ((prespectrumFunctor.map_comp _ _).symm.trans
        ((congrArg prespectrumFunctor.map (supportedNativeEvaluation_changeWeak f T a)).trans
          (prespectrumFunctor.map_comp _ _))).symm (supportedNativeFiberNull_evaluation f T a)
  have hs := ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatCoefficientSupportedFiberModel f T a)
    (W := asSmallCategory (acyclicStructure N)) (supportedNativeFiberAcyclicSmallEquivalence f T a)
    ((supportedNativeFiberToAcyclic_exact f T a).comp (acyclicStructure N).asSmall_up_exact)
    ((acyclicStructure N).asSmall_down_exact.comp (supportedNativeAcyclicToFiber_exact f T a))
    (supportedNativeFiberAcyclicModelMap f T a).property
  have ha := ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatCoefficientSupportedAmbientModel T a)
    (W := asSmallCategory (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen)
      AsSmall.equiv
    (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.asSmall_up_exact
    (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.asSmall_down_exact
    (supportedNativeAmbientModelMap T a).property
  have hc := (mappingConeMap_isStableEquivalence_of_excision
    (supportedNativeFiberEvaluationSquare f T a)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence _)
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _) hs ha).comp
    (supportedNative_canonicalCone_isStableEquivalence f T a)
  rw [he] at hc
  have ho := ExactModelEquivalence.isStableEquivalence
    (V := boundedAboveFlatCoefficientSupportedOpenModel f T a)
    (W := asSmallCategory (boundedAboveFlatCoefficientSupportedOpenModel f T a).obj.waldhausen)
      AsSmall.equiv
    (boundedAboveFlatCoefficientSupportedOpenModel f T a).obj.waldhausen.asSmall_up_exact
    (boundedAboveFlatCoefficientSupportedOpenModel f T a).obj.waldhausen.asSmall_down_exact
    (supportedNativeCoarseModelMap f T a).property
  intro d
  let : IsIso ((stableHomotopyFunctor d).map
      (prespectrumMap (supportedNativeCoarseModelMap f T a))) := ho d
  have hd := hc d
  rw [Functor.map_comp] at hd
  exact (isIso_comp_right_iff _ _).mp hd

end AlgebraicGeometry.Scheme.Modules

