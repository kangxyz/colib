/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeParameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.NativeParameterMap
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjective

/-! # Naturality of the original integral parameter comparison -/

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

/-- The abelian structure of the Nisnevich transfer sheaves in the integral parameter comparison. -/
local instance integralParameterNaturalityAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory

set_option quotPrecheck false in
local notation "N(" T ")" => projectiveDerivedMinusFunctor k (parameterTensorFunctor T)

set_option maxHeartbeats 850000 in
-- Compare the projective coefficient map with the original mate before reflection.
/-- The effective comparison carries an ordinary map of parameters to the
actual mate of restriction on the chosen projective models. -/
theorem effectiveNativeParameterCompIso_naturality
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    {T T' : SmoothSite (Spec (.of k))} [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom]
    (d : (F).flip.obj (Cor.mk T) ≅ Cor.parameterProduct T)
    (d' : (F).flip.obj (Cor.mk T') ≅ Cor.parameterProduct T')
    (f : T ⟶ T') (hf : (F).flip.map ((γ).map f) ≫ d'.hom = d.hom ≫ Cor.parameterProductMap f)
    (K : D) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    ((q).obj K ◁ (M).map ((γ).map f)) ≫ (effectiveNativeParameterCompIso e T' d').hom.app K =
      (effectiveNativeParameterCompIso e T d).hom.app K ≫
        (a ⋙ r).map ((projectiveCoefficientNatTrans k
          ((conjugateEquiv (parameterTensorAdjunction T') (parameterTensorAdjunction T)).symm
            (parameterPullbackNatTrans k f))).app K) := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let b := derivedConvolutionNativeParameterIso F T d
  let b' := derivedConvolutionNativeParameterIso F T' d'
  let n := (conjugateEquiv (parameterTensorAdjunction T') (parameterTensorAdjunction T)).symm
    (parameterPullbackNatTrans k f)
  let s := (sheafificationEffectiveReflectionIso k).symm
  let z := (projectiveDerivedMinusFunctorMap n).app K
  have hz : z = (projectiveCoefficientNatTrans k n).app K := by
    apply (DerivedCategory.Minus.ι (C := PST)).map_injective
    rw [projectiveDerivedMinusFunctorMap_map_app]
    exact (projectiveCoefficientNatTrans_app_hom k n K).symm
  let m := (singleDerivedMinus k 0).map ((representableLarge k).map ((γ).map f))
  let A := (effectiveRepresentedRightCompIso e T).hom.app K
  let A' := (effectiveRepresentedRightCompIso e T').hom.app K
  let p := (q).obj K ◁ (M).map ((γ).map f)
  let w := ((B).obj K).map m
  let u := s.hom.app (N(T).obj K)
  let u' := s.hom.app (N(T').obj K)
  let L := a ⋙ r
  have hA : p ≫ A' = A ≫ (q).map w :=
    effectiveRepresentedRightCompIso_naturality_parameter e f K
  have hb : w ≫ b'.hom.app K = b.hom.app K ≫ z :=
    derivedConvolutionNativeParameterIso_naturality F d d' f hf K
  have hq : (q).map w ≫ (q).map (b'.hom.app K) =
      (q).map (b.hom.app K) ≫ (q).map z :=
    (((q).map_comp _ _).symm.trans ((q).congr_map hb)).trans ((q).map_comp _ _)
  have hs : (q).map z ≫ u' = u ≫ L.map ((projectiveCoefficientNatTrans k n).app K) :=
    (s.hom.naturality z).trans (congrArg (fun t => u ≫ L.map t) hz)
  change p ≫ (A' ≫ (q).map (b'.hom.app K) ≫ u') =
    (A ≫ (q).map (b.hom.app K) ≫ u) ≫ L.map ((projectiveCoefficientNatTrans k n).app K)
  rw [reassoc_of% hA, reassoc_of% hq, hs]
  simp only [Category.assoc]

end AlgebraicGeometry.MotivicHomotopy
