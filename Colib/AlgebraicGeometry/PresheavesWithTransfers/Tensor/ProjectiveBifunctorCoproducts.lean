/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingleNaturality
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionCoproducts
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedConvolution
import Colib.CategoryTheory.Preadditive.AdditiveFunctorGrothendieck
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import StacksFrontier.Homology.DerivedCategory.LocallySmall
import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts

/-!
# Direct sums of projective singles under convolution

For a fixed left projective complex, the signed total and the derived
quotient preserve the native cofan of projective single complexes.
The comparison with the selected projective representative is natural
for the original coprojections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.ProjectionFormulaQCohCoproducts

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ

variable [HasDerivedCategory.{w} PST(k)]
variable (F : PST(k) ⥤ PST(k) ⥤ PST(k)) [F.Additive] [∀ P, (F.obj P).Additive]

/-- The derived right slot sends the original coproduct of projective singles to a coproduct. -/
theorem projectiveDerivedMinusBifunctor_preservesSingleCoproduct_right
    (K : DerivedCategory.Minus PST(k)) {I : Type (u + 1)} (A : I → PST(k)) (n : ℤ)
    [∀ i, Projective (A i)]
    (hF : ∀ P, PreservesColimitsOfShape (Discrete I) (F.obj P)) :
    PreservesColimit (Discrete.functor fun i => (singleDerivedMinus k n).obj (A i))
      ((projectiveDerivedMinusBifunctor F).obj K ⋙ DerivedCategory.Minus.ι) := by
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfShape
  let : HasColimitsOfShape (Discrete I) ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    functorCategoryHasColimitsOfShape
  let : HasColimitsOfShape (Discrete I) PST(k) := hasColimitsOfShape_of_closedUnderColimits _
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})
  let : ∀ P, PreservesColimitsOfShape (Discrete I) (F.obj P) := hF
  let S := CochainComplex.singleFunctor PST(k) n
  let E := boundedAboveProjectiveEquivalence k
  let Q := HomotopyCategory.quotient PST(k) c
  let DQ := DerivedCategory.Q (C := PST(k))
  let HQ := DerivedCategory.Qh (C := PST(k))
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let B := (projectiveDerivedMinusBifunctor F).obj K
  let P := (E.inverse.obj K).obj.as
  let T := (F.map₂CochainComplex).obj P
  let D := Discrete.functor fun i => (singleDerivedMinus k n).obj (A i)
  let C' := Cofan.mk (S.obj (∐ A)) (fun i => S.map (Sigma.ι A i))
  have hC' : IsColimit C' := isColimitOfHasCoproductOfPreservesColimit S A
  let : PreservesColimit (Discrete.functor fun i => S.obj (A i)) T :=
    preservesColimit_map₂HomologicalComplex_obj F P _
  let : PreservesColimitsOfShape (Discrete I) DQ :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts PST(k) I
  have hTot : IsColimit ((T ⋙ DQ).mapCocone C') := isColimitOfPreserves _ hC'
  let Y (a : PST(k)) [Projective a] : (B ⋙ V).obj ((singleDerivedMinus k n).obj a) ≅
      DQ.obj (T.obj (S.obj a)) :=
    let H := (projectiveHomotopyBifunctorToDerivedMinus F).obj (E.inverse.obj K) ⋙ V
    H.mapIso (singleProjectiveComparison a n) ≪≫
      (DerivedCategory.quotientCompQhIso PST(k)).app (T.obj (S.obj a))
  let e : D ⋙ (B ⋙ V) ≅ (Discrete.functor (fun i => S.obj (A i))) ⋙ (T ⋙ DQ) :=
    Discrete.natIso (fun i => Y (A i.as))
  apply preservesColimit_of_preserves_colimit_cocone (singleDerivedMinusCofanIsColimit k A n)
  apply ((IsColimit.precomposeHomEquiv e _).symm hTot).ofIsoColimit
  refine Cocone.ext (Y (∐ A)).symm (fun i => ?_)
  have hg := singleProjectiveComparison_naturality (Sigma.ι A i.as) n
  let H := (projectiveHomotopyBifunctorToDerivedMinus F).obj (E.inverse.obj K) ⋙ V
  have h := congrArg H.map hg
  rw [H.map_comp, H.map_comp] at h
  have hh := (DerivedCategory.quotientCompQhIso PST(k)).hom.naturality
    (T.map (S.map (Sigma.ι A i.as)))
  change HQ.map (Q.map (T.map (S.map (Sigma.ι A i.as)))) ≫
      (DerivedCategory.quotientCompQhIso PST(k)).hom.app _ =
    (DerivedCategory.quotientCompQhIso PST(k)).hom.app _ ≫
      DQ.map (T.map (S.map (Sigma.ι A i.as))) at hh
  apply (cancel_mono (Y (∐ A)).hom).1
  simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, Category.assoc]
  have hY : (Y (∐ A)).symm.hom ≫ (Y (∐ A)).hom = 𝟙 _ := (Y (∐ A)).inv_hom_id
  rw [hY]
  let g := DQ.map (T.map (S.map (Sigma.ι A i.as)))
  let y := (Y (A i.as)).hom
  let P₀ := DQ.obj (T.obj (S.obj (∐ A)))
  let m := H.map (E.inverse.map ((singleDerivedMinus k n).map (Sigma.ι A i.as)))
  let η := (Y (∐ A)).hom
  change y ≫ g ≫ 𝟙 P₀ = m ≫ η
  have hi : g ≫ 𝟙 P₀ = g := Category.comp_id g
  rw [hi]
  change (Y (A i.as)).hom ≫ DQ.map (T.map (S.map (Sigma.ι A i.as))) =
    H.map (E.inverse.map ((singleDerivedMinus k n).map (Sigma.ι A i.as))) ≫ (Y (∐ A)).hom
  let π := DerivedCategory.quotientCompQhIso PST(k)
  let x := H.map (singleProjectiveComparison (A i.as) n).hom
  let z := H.map (singleProjectiveComparison (∐ A) n).hom
  let a := π.hom.app (T.obj (S.obj (A i.as)))
  let b := π.hom.app (T.obj (S.obj (∐ A)))
  let t := HQ.map (Q.map (T.map (S.map (Sigma.ι A i.as))))
  change (x ≫ a) ≫ g = m ≫ (z ≫ b)
  have ht : t ≫ b = a ≫ g := hh
  have hz : m ≫ z = x ≫ t := h
  exact (Category.assoc _ _ _).trans
    ((congrArg (x ≫ ·) ht.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ b) hz.symm).trans (Category.assoc _ _ _))))

variable (G : Cor k ⥤ Cor k ⥤ Cor k) [G.Additive] [∀ X, (G.obj X).Additive]

omit [G.Additive] [∀ X, (G.obj X).Additive] in
/-- In the varying right argument, derived convolution preserves the represented single cofan. -/
theorem derivedConvolution_preservesRepresentableSingleCoproduct_right
    (K : DerivedCategory.Minus PST(k)) (I : Type (u + 1)) (A : I → Cor k) (n : ℤ) :
    PreservesColimit
      (Discrete.functor fun i => (singleDerivedMinus k n).obj ((representableLarge k).obj (A i)))
      ((derivedConvolution G).obj K ⋙ DerivedCategory.Minus.ι) :=
  projectiveDerivedMinusBifunctor_preservesSingleCoproduct_right (convolutionBifunctor G) K
    (fun i => (representableLarge k).obj (A i)) n
    (fun P => convolution_preservesCoproducts_right G P I)

end AlgebraicGeometry.PresheafWithTransfers
