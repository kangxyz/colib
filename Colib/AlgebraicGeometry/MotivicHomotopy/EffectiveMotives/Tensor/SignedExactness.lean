/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.CoherentConvolution
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSignedExactness

/-!
# Exactness for the signed effective tensor shift

The original cone comparison commutes with the shift descended along the
homotopy quotient. The projective equivalence and monoidal localization
therefore give exactness for the specified signed tensor shift.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)]

local notation "PST(" K ")" => TransferCoefficients K
local notation "B(" K ")" => convolutionBifunctor (curriedTensor (Cor K))
local notation "P(" K ")" => boundedAboveProjectiveCondition K
local notation "J(" K ")" => BoundedAboveProjectiveHomotopy K

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  convolutionHomotopyCommShift₂Int boundedAboveProjectiveCondition_convolution_isMonoidal

section Derived

variable [HasDerivedCategory.{w} PST(k)]

set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST(k)
local notation "E" => boundedAboveProjectiveEquivalence k

attribute [local instance] convolutionProjectiveCommShift₂Int

omit [HasDerivedCategory PST(k)] in
private theorem projectiveTensorLeft_isTriangulated (K : J(k)) :
    (tensorLeft K).IsTriangulated := by
  let I := (P(k)).ι
  let : (tensorLeft (I.obj K)).IsTriangulated :=
    signedTotalHomotopyBifunctor_obj_isTriangulated (B(k)) (I.obj K)
  let e : tensorLeft K ⋙ I ≅ I ⋙ tensorLeft (I.obj K) := Iso.refl _
  let : (tensorLeft K).CommShift ℤ := Functor.CommShift.ofComp e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 inferInstance

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionCommShift₂Int

set_option maxHeartbeats 700000 in
-- The selected derived shift is the composite of the original projective shifts.
/-- Right-variable exactness for the specified derived Koszul shift. -/
theorem derivedSignedTensorLeft_isTriangulated (K : D) : (tensorLeft K).IsTriangulated := by
  let I := (E).inverse
  let V := (E).functor
  let B := tensorLeft (I.obj K)
  let T : D ⥤ D := (I ⋙ B) ⋙ V
  let e : T ≅ tensorLeft K := Iso.refl _
  let : B.IsTriangulated := projectiveTensorLeft_isTriangulated (I.obj K)
  let : (I ⋙ B).IsTriangulated := inferInstance
  let : T.IsTriangulated := inferInstanceAs (((I ⋙ B) ⋙ V).IsTriangulated)
  let : NatTrans.CommShift e.hom ℤ := by
    refine ⟨fun n => NatTrans.ext (funext fun X => ?_)⟩
    let a := (T.commShiftIso n).hom.app X
    let b := ((tensorLeft K).commShiftIso n).hom.app X
    have hab : a = b := rfl
    change a ≫ (shiftFunctor D n).map (𝟙 (T.obj X)) = 𝟙 (T.obj (X⟦n⟧)) ≫ b
    calc
      _ = a ≫ 𝟙 _ := congrArg (a ≫ ·) ((shiftFunctor D n).map_id (T.obj X))
      _ = a := Category.comp_id a
      _ = b := hab
      _ = _ := (Category.id_comp b).symm
  exact Functor.isTriangulated_of_iso e

end Derived

end AlgebraicGeometry.PresheafWithTransfers

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

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

/-- The abelian structure of the transfer sheaves underlying effective tensor exactness. -/
local instance signedExactnessAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

variable (e : ∀ T : SmoothSite (Spec (.of k)),
  Cor.graphFunctor k ⋙ (curriedTensor (Cor k)).flip.obj (Cor.mk T) ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionCommShift₂Int

/-- Right-variable exactness for the specified effective Koszul shift. -/
theorem effectiveSignedTensorLeft_isTriangulated (K : E) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionCommShift₂Int e
    (tensorLeft K).IsTriangulated := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionCommShift₂Int e
  let : (q).Monoidal := (effectiveSignedConvolutionLocalizationCoreMonoidal e).toMonoidal
  let : Functor.LaxMonoidal.CommShift q ℤ :=
    effectiveSignedConvolutionLocalizationMonoidalCommShift e
  let _ := Localization.essSurj q W
  let _ := Localization.essSurj_mapArrow q W
  let P := (q).objPreimage K
  let i := (q).objObjPreimageIso K
  let a := Functor.Monoidal.commTensorLeft q P
  let T := tensorLeft ((q).obj P)
  let T' := tensorLeft K
  let : (tensorLeft P).IsTriangulated := derivedSignedTensorLeft_isTriangulated P
  let : NatTrans.CommShift a.hom ℤ := Functor.LaxMonoidal.CommShift.commShift_μNatTransSnd P
  let : T.IsTriangulated := Functor.isTriangulated_of_precomp_iso a
  let j : T ≅ T' := (curriedTensor E).mapIso i
  let : NatTrans.CommShift j.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor E).map i.hom) ℤ)
  exact Functor.isTriangulated_of_iso j

/-- The original effective tensor is additive in both variables by signed
left tensor exactness and naturality of the symmetry. -/
theorem effectiveSignedConvolutionMonoidalPreadditive :
    letI := effectiveSignedConvolutionMonoidalCategory e
    MonoidalPreadditive E := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionCommShift₂Int e
  let := effectiveSignedConvolutionSymmetricCategory e
  let h₁ (X : E) : (tensorLeft X).Additive := by
    let : (tensorLeft X).IsTriangulated := effectiveSignedTensorLeft_isTriangulated e X
    infer_instance
  let h₂ (Y : E) : (tensorRight Y).Additive := by
    let : (tensorLeft Y).Additive := h₁ Y
    exact Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight Y)
  exact
    { whiskerLeft_zero := fun {X Y Z} => by
        let := h₁ X
        exact Functor.map_zero (tensorLeft X) Y Z
      zero_whiskerRight := fun {X Y Z} => by
        let := h₂ X
        exact Functor.map_zero (tensorRight X) Y Z
      whiskerLeft_add := fun {X _ _} f g => by
        let := h₁ X
        exact Functor.map_add (tensorLeft X) (f := f) (g := g)
      add_whiskerRight := fun {X _ _} f g => by
        let := h₂ X
        exact Functor.map_add (tensorRight X) (f := f) (g := g) }

end AlgebraicGeometry.MotivicHomotopy
