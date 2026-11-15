/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.RightTensorShift
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.TorusProjectorShift
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-! # The signed shift of the original Lefschetz comparison -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers
open SmoothSite SmoothSite.Contraction

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "E" => EffectiveMotivesMinus k
local notation "q" => singularPresheafToEffective k
local notation "W" => effectivePresheafEquivalences k
local notation "a" => derivedNisnevichSheafification k
local notation "r" => effectiveReflection k
local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "T" => effectiveReducedTorusTensorFunctor k

/-- The abelian structure of the transfer sheaves used in the reduced torus shift comparison. -/
local instance lefschetzComparisonShiftAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable (e : ∀ X : SmoothSite (Spec (CommRingCat.of k)),
  Cor.graphFunctor k ⋙ (curriedTensor (Cor k)).flip.obj (Cor.mk X) ≅
    SmoothSite.Contraction.parameterProduct X ⋙ Cor.graphFunctor k)

variable
  (d : (curriedTensor (Cor k)).flip.obj
      (Cor.mk (multiplicativeGroupObject (Spec (CommRingCat.of k)))) ≅
    Cor.parameterProduct (multiplicativeGroupObject (Spec (CommRingCat.of k))))
  (b : (curriedTensor (Cor k)).flip.obj (Cor.mk (base (Spec (CommRingCat.of k)))) ≅
    Cor.parameterProduct (base (Spec (CommRingCat.of k))))

variable
  (hu : (curriedTensor (Cor k)).flip.map
      ((Cor.graphFunctor k).map (SmoothSite.torusOne (Spec (CommRingCat.of k)))) ≫ d.hom =
    b.hom ≫ Cor.parameterProductMap (SmoothSite.torusOne (Spec (CommRingCat.of k))))
  (hp : (curriedTensor (Cor k)).flip.map
      ((Cor.graphFunctor k).map (toBase (multiplicativeGroupObject (Spec (CommRingCat.of k))))) ≫
        b.hom =
    d.hom ≫ Cor.parameterProductMap (toBase (multiplicativeGroupObject (Spec (CommRingCat.of k)))))

local notation "p" => projectiveReducedTorusTensorQuotient k

variable {R₀ : EffectiveMotivesMinus k}
  (s : Retract R₀ ((effectiveMotive k).obj
    (Cor.mk (multiplicativeGroupObject (Spec (CommRingCat.of k))))))
  (hs : s.r ≫ s.i = 𝟙 _ - (effectiveMotive k).map ((Cor.graphFunctor k).map
    (toBase (multiplicativeGroupObject (Spec (CommRingCat.of k))) ≫
      SmoothSite.torusOne (Spec (CommRingCat.of k)))))

set_option maxHeartbeats 600000 in
-- Fix the endpoints of the composed shift comparisons before composing them.
/-- The reduction comparison preserves the actual first-variable shift on presheaf models. -/
private theorem reducedTorusCompIso_commShift
    (hC : letI := effectiveSignedConvolutionMonoidalCategory e
      letI := effectiveSignedConvolutionCommShift₂Int e
      NatTrans.CommShift (effectiveNativeParameterCompIso e G d).hom ℤ) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionCommShift₂Int e
    NatTrans.CommShift (reducedTorusCompIso e d b hu hp s hs).hom ℤ := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionCommShift₂Int e
  let C := effectiveNativeParameterCompIso e G d
  let j := (curriedTensor E).flip.map s.i
  let U := projectiveDerivedMinusFunctor k (parameterTensorFunctor G)
  let Q : U ⋙ a ⟶ projectiveReducedTorusTensorToDerivedMinus k := p
  let : NatTrans.CommShift p ℤ := projectiveReducedTorusTensorQuotient_commShift k
  let : NatTrans.CommShift Q ℤ := by
    refine ⟨fun n => NatTrans.ext (funext fun X => ?_)⟩
    change ((U ⋙ a).commShiftIso n).hom.app X ≫ (Q.app X)⟦n⟧' =
      Q.app (X⟦n⟧) ≫ ((projectiveReducedTorusTensorToDerivedMinus k).commShiftIso n).hom.app X
    rw [← projectiveTorusTensorToDerivedMinus_commShiftIso_hom_app]
    exact NatTrans.shift_app_comm p n X
  let : NatTrans.CommShift C.hom ℤ := hC
  let : NatTrans.CommShift j ℤ := inferInstanceAs (NatTrans.CommShift
    ((curriedTensor E).flip.map s.i) ℤ)
  let s₀ := Functor.whiskerLeft q j
  let A := Functor.associator U a r
  let Q₀ := Functor.whiskerRight Q r
  let Q₁ := A.inv ≫ Q₀
  let : NatTrans.CommShift s₀ ℤ :=
    NatTrans.CommShift.whiskerLeft (F₁ := q) (tensorRight R₀)
      (tensorRight ((effectiveMotive k).obj (Cor.mk G))) j ℤ
  let : NatTrans.CommShift A.inv ℤ := NatTrans.CommShift.of_iso_inv A ℤ
  let : NatTrans.CommShift Q₀ ℤ := NatTrans.CommShift.whiskerRight Q r ℤ
  let : NatTrans.CommShift Q₁ ℤ := NatTrans.CommShift.comp A.inv Q₀ ℤ
  have hQ : Q₁ = Functor.whiskerRight p r := by
    apply NatTrans.ext
    funext X
    simp only [Q₁, Q₀, Q, A, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp]
  let : NatTrans.CommShift (C.hom ≫ Q₁) ℤ := NatTrans.CommShift.comp C.hom Q₁ ℤ
  rw [reducedTorusCompIso_hom e d b hu hp s hs, ← hQ]
  exact NatTrans.CommShift.comp s₀ (C.hom ≫ Q₁) ℤ

/-- The unshifted reduced comparison commutes with shift when its native parameter
comparison and the original projective adjunction comparison do. -/
theorem effectiveRightReducedTorusIso_commShift
    (hC : letI := effectiveSignedConvolutionMonoidalCategory e
      letI := effectiveSignedConvolutionCommShift₂Int e
      NatTrans.CommShift (effectiveNativeParameterCompIso e G d).hom ℤ)
    (h : NatTrans.CommShift (projectiveEffectiveTorusNatIso k).hom ℤ) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionCommShift₂Int e
    NatTrans.CommShift (effectiveRightReducedTorusIso e d b hu hp s hs).hom ℤ := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionCommShift₂Int e
  let := Localization.essSurj q W
  let f := effectiveRightReducedTorusIso e d b hu hp s hs
  let C := reducedTorusCompIso e d b hu hp s hs
  let A := projectiveEffectiveTorusNatIso k
  let g := sheafificationEffectiveReflectionIso k
  let := h
  let : NatTrans.CommShift C.hom ℤ := reducedTorusCompIso_commShift e d b hu hp s hs hC
  let : NatTrans.CommShift g.hom ℤ := Functor.CommShift.ofIso_compatibility g ℤ
  apply NatTrans.commShift_of_whiskerLeft q f.hom
  have H : Functor.whiskerLeft q f.hom = C.hom ≫ A.hom ≫ Functor.whiskerRight g.hom T := by
    apply NatTrans.ext
    funext X
    change f.hom.app ((q).obj X) = C.hom.app X ≫ A.hom.app X ≫ (T).map (g.hom.app X)
    dsimp only [C]
    rw [reducedTorusCompIso_hom e d b hu hp s hs]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    exact effectiveRightReducedTorusIso_hom_app_localized e d b hu hp s hs X
  rw [H]
  infer_instance

/-- The canonical signed Lefschetz comparison commutes with both original one-variable
shift structures once the unshifted quotient comparison is checked. -/
theorem effectiveRightLefschetzIso_commShift_of_reduced
    (h : letI := effectiveSignedConvolutionMonoidalCategory e
      letI := effectiveSignedConvolutionCommShift₂Int e
      NatTrans.CommShift (effectiveRightReducedTorusIso e d b hu hp s hs).hom ℤ) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionCommShift₂Int e
    NatTrans.CommShift (effectiveRightLefschetzIso e d b hu hp s hs).hom ℤ := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionCommShift₂Int e
  let := h
  let := effectiveTensorRightShiftIso_commShift e R₀ 1
  change NatTrans.CommShift ((effectiveTensorRightShiftIso e R₀ 1).hom ≫
    Functor.whiskerRight (effectiveRightReducedTorusIso e d b hu hp s hs).hom
      (shiftFunctor E (1 : ℤ))) ℤ
  infer_instance

end AlgebraicGeometry.MotivicHomotopy
