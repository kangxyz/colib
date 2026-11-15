/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionSwap
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionCoproducts
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionRepresentable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctor
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveRepresentable
import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Projective coefficients are closed under convolution

Every projective coefficient is a retract of a sum of the original
representables. The represented product comparison and coproduct
preservation identify the tensor of such projectives as projective.
The native signed total then has projective terms as well.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ

variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive] [∀ Y, (F.obj Y).Additive]
variable (s : F ≅ F.flip) (hs : ∀ Y Z, (s.hom.app Y).app Z ≫ (s.hom.app Z).app Y = 𝟙 _)

private instance (I : Type (u + 1)) : HasColimitsOfShape (Discrete I) PST(k) := by
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfShape
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I)
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})

omit [F.Additive] [∀ Y, (F.obj Y).Additive] in
include s hs in
/-- The symmetry transfers coproduct preservation to the varying left argument. -/
theorem convolution_preservesCoproducts_left (Q : PST(k)) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) ((convolutionBifunctor F).flip.obj Q) := by
  let : PreservesColimitsOfShape (Discrete I) ((convolutionBifunctor F).obj Q) :=
    convolution_preservesCoproducts_right F Q I
  exact preservesColimitsOfShape_of_natIso ((convolutionSwap F s hs).app Q)

private theorem projective_obj_of_representables (G : PST(k) ⥤ PST(k))
    (hG : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G)
    (hR : ∀ X : Cor k, Projective (G.obj ((representableLarge k).obj X)))
    (P : PST(k)) [Projective P] : Projective (G.obj P) := by
  let I : Type (u + 1) := Σ X : Cor k, sections P X
  let R : I → PST(k) := fun i => (representableLarge k).obj i.1
  let : PreservesColimitsOfShape (Discrete I) G := hG I
  let : ∀ i : I, Projective (G.obj (R i)) := fun i => hR i.1
  let e := PreservesCoproduct.iso G R
  let : Projective (G.obj (∐ R)) :=
    Projective.of_iso e.symm (Projective.instSigmaObj (fun i => G.obj (R i)))
  exact ((retractRepresentableLargeCoproduct P).map G).projective

include s hs in
/-- Convolution takes two projective coefficients to a projective coefficient. -/
theorem convolution_projective (P Q : PST(k)) [Projective P] [Projective Q] :
    Projective (convolutionPresheaf F P Q) := by
  let G := (convolutionBifunctor F).obj P
  apply projective_obj_of_representables G (convolution_preservesCoproducts_right F P) _ Q
  intro Y
  let R := (representableLarge k).obj Y
  let H := (convolutionBifunctor F).flip.obj R
  apply projective_obj_of_representables H (convolution_preservesCoproducts_left F s hs R) _ P
  intro X
  exact Projective.of_iso (convolutionRepresentableIso F X Y).symm inferInstance

private instance (I : Type) : HasColimitsOfShape (Discrete I) PST(k) := by
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfShape
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I)
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})

include s hs in
/-- Each native signed total term of two projective complexes is projective. -/
theorem convolutionTotal_projective (K L : CochainComplex PST(k) ℤ)
    [∀ i, Projective (K.X i)] [∀ i, Projective (L.X i)] (n : ℤ) :
    Projective (mapBifunctor K L (convolutionBifunctor F) c |>.X n) := by
  let T := (((convolutionBifunctor F).mapBifunctorHomologicalComplex c c).obj K).obj L
  let I := ↥(ComplexShape.π c c c ⁻¹' {n})
  let W : I → PST(k) := T.toGradedObject.mapObjFun (ComplexShape.π c c c) n
  let h (i : I) : Projective (W i) :=
    convolution_projective F s hs (K.X i.val.1) (L.X i.val.2)
  change Projective (∐ W)
  constructor
  intro X Y f g hg
  let lift (i : I) : W i ⟶ X :=
    let := h i
    Projective.factorThru (Sigma.ι W i ≫ f) g
  refine ⟨Sigma.desc lift, ?_⟩
  apply Sigma.hom_ext
  intro i
  let := h i
  rw [Sigma.ι_comp_desc_assoc]
  exact Projective.factorThru_comp (Sigma.ι W i ≫ f) g

end AlgebraicGeometry.PresheafWithTransfers
