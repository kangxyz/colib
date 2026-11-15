/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.CoherentConvolution
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterMap
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionParameterMap
public import Mathlib.CategoryTheory.Functor.Category

/-! # Effective tensor with a native represented parameter -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => EffectiveMotivesMinus k
set_option quotPrecheck false in
local notation "q" => singularPresheafToEffective k
local notation "a" => derivedNisnevichSheafification k
local notation "M" => effectiveMotive k
local notation "r" => effectiveReflection k
local notation "F" => curriedTensor (Cor k)
local notation "B" => derivedConvolution F
local notation "γ" => Cor.graphFunctor k
set_option quotPrecheck false in
local notation "R(" T ")" => (singleDerivedMinus k 0).obj ((representableLarge k).obj (Cor.mk T))

/-- The abelian structure of the transfer sheaves used in the represented parameter comparison. -/
local instance : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory

set_option maxHeartbeats 900000 in
-- The tensorator uses the specified localized monoidal data.
/-- The actual tensor with a represented parameter on localized transfer complexes. -/
def effectiveRepresentedRightCompIso
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    (T : SmoothSite (Spec (.of k))) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    q ⋙ tensorRight ((M).obj (Cor.mk T)) ≅ ((B).flip.obj (R(T))) ⋙ q :=
  letI := effectiveSignedConvolutionMonoidalCategory e
  let I := localizedRepresentableIso (k := k) (Cor.mk T)
  let C := effectiveSignedConvolutionLocalizationCoreMonoidal e
  letI := C.toMonoidal
  let b := derivedConvolutionTensorIso (k := k)
  Functor.isoWhiskerLeft q ((curriedTensor E).flip.mapIso I.symm) ≪≫
    Functor.Monoidal.commTensorRight q (R(T)) ≪≫
    Functor.isoWhiskerRight (((CategoryTheory.flipFunctor D D D).mapIso b).app (R(T))) q

set_option maxHeartbeats 950000 in
-- Compare the literal representable maps and the original localization tensorator.
/-- The effective represented comparison carries maps of the parameter correspondence. -/
theorem effectiveRepresentedRightCompIso_naturality_parameter
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    {T T' : SmoothSite (Spec (.of k))} (f : T ⟶ T') (K : D) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    ((q).obj K ◁ (M).map ((γ).map f)) ≫ (effectiveRepresentedRightCompIso e T').hom.app K =
      (effectiveRepresentedRightCompIso e T).hom.app K ≫
        (q).map (((B).obj K).map
          ((singleDerivedMinus k 0).map ((representableLarge k).map ((γ).map f)))) := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let I := localizedRepresentableIso (k := k) (Cor.mk T)
  let I' := localizedRepresentableIso (k := k) (Cor.mk T')
  let C := effectiveSignedConvolutionLocalizationCoreMonoidal e
  let b := derivedConvolutionTensorIso (k := k)
  let m := (singleDerivedMinus k 0).map ((representableLarge k).map ((γ).map f))
  have h₀ : (q).map m ≫ I'.hom = I.hom ≫ (M).map ((γ).map f) :=
    localizedRepresentableIso_naturality ((γ).map f)
  have h : (M).map ((γ).map f) ≫ I'.inv = I.inv ≫ (q).map m :=
    (I'.comp_inv_eq).2 (((I.inv_comp_eq).2 h₀).symm.trans (Category.assoc _ _ _).symm)
  have ht :
      ((q).obj K ◁ (M).map ((γ).map f)) ≫ ((q).obj K ◁ I'.inv) =
        ((q).obj K ◁ I.inv) ≫ ((q).obj K ◁ (q).map m) := by
    exact ((whiskerLeft_comp _ _ _).symm.trans (congrArg ((q).obj K ◁ ·) h)).trans
      (whiskerLeft_comp _ _ _)
  have hμ :
      ((q).obj K ◁ (q).map m) ≫ (C.μIso K (R(T'))).hom =
        (C.μIso K (R(T))).hom ≫ (q).map (K ◁ m) := C.μIso_hom_natural_right K m
  have hb : (K ◁ m) ≫ ((b.hom.app K).app (R(T'))) =
      ((b.hom.app K).app (R(T))) ≫ ((B).obj K).map m := (b.hom.app K).naturality m
  have hb' : (q).map (K ◁ m) ≫ (q).map ((b.hom.app K).app (R(T'))) =
      (q).map ((b.hom.app K).app (R(T))) ≫ (q).map (((B).obj K).map m) :=
    (((q).map_comp _ _).symm.trans ((q).congr_map hb)).trans ((q).map_comp _ _)
  change ((q).obj K ◁ (M).map ((γ).map f)) ≫ ((q).obj K ◁ I'.inv) ≫
      (C.μIso K (R(T'))).hom ≫ (q).map ((b.hom.app K).app (R(T'))) =
    (((q).obj K ◁ I.inv) ≫ (C.μIso K (R(T))).hom ≫ (q).map ((b.hom.app K).app (R(T)))) ≫
      (q).map (((B).obj K).map m)
  rw [reassoc_of% ht, reassoc_of% hμ, hb']
  simp only [Category.assoc]

set_option maxHeartbeats 750000 in
-- Both comparisons use the same projective coefficient functor before localization.
/-- For any smooth parameter the original affine-line descended pushforward is
right tensor by the actual represented effective motive. -/
def effectiveRepresentedRightParameterIso
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    (T : SmoothSite (Spec (.of k))) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    tensorRight ((M).obj (Cor.mk T)) ≅ effectiveParameterTensor (e T) :=
  letI := effectiveSignedConvolutionMonoidalCategory e
  let W := effectivePresheafEquivalences k
  let P := (F).flip.obj (Cor.mk T)
  let b := derivedParameterPushforward P ⋙ q
  let X := tensorRight ((M).obj (Cor.mk T))
  let Y := effectiveParameterTensor (e T)
  let h : q ⋙ X ≅ b := effectiveRepresentedRightCompIso e T ≪≫
    Functor.isoWhiskerRight (derivedConvolutionParameterIso F (Cor.mk T)) q
  letI : Localization.Lifting q W b X := ⟨h⟩
  letI : Localization.Lifting q W b Y := ⟨effectiveParameterTensorCompIso (e T)⟩
  Localization.liftNatIso q W b b X Y (Iso.refl _)

set_option maxHeartbeats 750000 in
-- Evaluate the actual two liftings at the original presheaf complex.
/-- On localized complexes the represented comparison is the original signed convolution
comparison followed by the effective comparison for the actual coend. -/
theorem effectiveRepresentedRightParameterIso_hom_app_localized
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    (T : SmoothSite (Spec (.of k))) (K : D) :
    (effectiveRepresentedRightParameterIso e T).hom.app ((q).obj K) =
      (effectiveRepresentedRightCompIso e T).hom.app K ≫
        (q).map ((derivedConvolutionParameterIso F (Cor.mk T)).hom.app K) ≫
          (effectiveParameterTensorCompIso (e T)).inv.app K := by
  rw [effectiveRepresentedRightParameterIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.assoc]

set_option maxHeartbeats 700000 in
-- The intersection of the two localization comparisons appears in their naturality square.
/-- The monoidal right-parameter comparison carries the original parameter correspondence to
its effective coend mate. -/
theorem effectiveRepresentedRightParameterIso_naturality
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    {T T' : SmoothSite (Spec (.of k))} (f : T ⟶ T') (A : E) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (A ◁ (M).map ((γ).map f)) ≫ (effectiveRepresentedRightParameterIso e T').hom.app A =
      (effectiveRepresentedRightParameterIso e T).hom.app A ≫
        (effectiveParameterTensorMap (e T) (e T') ((F).flip.map ((γ).map f))).app A := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let θ := effectiveParameterTensorMap (e T) (e T') ((F).flip.map ((γ).map f))
  let η := effectiveRepresentedRightParameterIso e T
  let η' := effectiveRepresentedRightParameterIso e T'
  let t := (curriedTensor E).flip.map ((M).map ((γ).map f))
  suffices h : t ≫ η'.hom = η.hom ≫ θ by
    exact NatTrans.congr_app h A
  apply Localization.natTrans_ext q (effectivePresheafEquivalences k)
  intro K
  let m := (singleDerivedMinus k 0).map ((representableLarge k).map ((γ).map f))
  let n := projectiveDerivedMinusFunctorMap
    (coendPushforwardParameterMap ((F).flip.map ((γ).map f)))
  let c := derivedConvolutionParameterIso F (Cor.mk T)
  let c' := derivedConvolutionParameterIso F (Cor.mk T')
  have h₁ := effectiveRepresentedRightCompIso_naturality_parameter e f K
  have h₂ : ((B).obj K).map m ≫ c'.hom.app K = c.hom.app K ≫ n.app K :=
    derivedConvolutionParameterIso_naturality_right F ((γ).map f) K
  change ((q).obj K ◁ (M).map ((γ).map f)) ≫ η'.hom.app ((q).obj K) =
    η.hom.app ((q).obj K) ≫ θ.app ((q).obj K)
  rw [effectiveRepresentedRightParameterIso_hom_app_localized,
    effectiveRepresentedRightParameterIso_hom_app_localized,
    effectiveParameterTensorMap_app_localized]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% h₁, ← (q).map_comp_assoc, h₂, (q).map_comp, Category.assoc]

set_option quotPrecheck false in
local notation "N(" T ")" => projectiveDerivedMinusFunctor k (parameterTensorFunctor T)
local notation "Nₑ(" T ")" => N(T) ⋙ a ⋙ r

/-- On the original localized presheaf models, an effective represented
right tensor is their native parameter pushforward. -/
def effectiveNativeParameterCompIso
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
    (d : (F).flip.obj (Cor.mk T) ≅ Cor.parameterProduct T) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    q ⋙ tensorRight ((M).obj (Cor.mk T)) ≅ Nₑ(T) :=
  effectiveRepresentedRightCompIso e T ≪≫
    Functor.isoWhiskerRight (derivedConvolutionNativeParameterIso F T d) q ≪≫
    Functor.isoWhiskerLeft N(T) (sheafificationEffectiveReflectionIso k).symm

end AlgebraicGeometry.MotivicHomotopy
