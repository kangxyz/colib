/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.ReducedRepresentable
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ProjectiveComparison
public import Mathlib.Algebra.Homology.HomotopyCategory
import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor

/-!
# Reduced torus tensor on projective representatives

Apply the original reduced coefficient tensor termwise on the
bounded-above projective model, followed by exact Nisnevich
sheafification. The original quotient and its section still split.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

private instance : ((nisnevichSheafify k).mapDerivedCategoryMinus).Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact ((nisnevichSheafify k).mapDerivedCategory).map_add

/-- The actual reduced tensor of projective coefficients followed by
exact Nisnevich sheafification. -/
def projectiveReducedTorusTensorToDerivedMinus :
    DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory.Minus (SheafWithTransfers.{u + 1} k) :=
  projectiveDerivedMinusFunctor k (reducedParameterTensorFunctor k) ⋙
    (nisnevichSheafify k).mapDerivedCategoryMinus

/-- Apply the original parameter morphism termwise to the chosen
projective representatives. -/
@[no_expose]
def projectiveCoefficientNatTrans
    {F G : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k}
    [F.Additive] [G.Additive] (η : F ⟶ G) :
    projectiveDerivedMinusFunctor k F ⟶ projectiveDerivedMinusFunctor k G := by
  let c := ComplexShape.up ℤ
  let I := (boundedAboveProjectiveCondition k).ι
  let E := (boundedAboveProjectiveEquivalence k).inverse
  let τ := Functor.whiskerRight (η.mapHomotopyCategory c) DerivedCategory.Qh
  let τ' := Functor.whiskerLeft I τ
  unfold projectiveDerivedMinusFunctor
  apply Functor.whiskerLeft E
  unfold projectiveHomotopyMapToDerivedMinus
  refine { app := fun K => ObjectProperty.homMk (τ'.app K), naturality := ?_ }
  intro K L f
  apply ObjectProperty.hom_ext
  exact τ'.naturality f

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
@[simp]
theorem projectiveCoefficientNatTrans_app_hom
    {F G : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k}
    [F.Additive] [G.Additive] (η : F ⟶ G)
    (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) :
    ((projectiveCoefficientNatTrans k η).app K).hom =
      DerivedCategory.Qh.map ((η.mapHomotopyCategory (.up ℤ)).app
        ((boundedAboveProjectiveEquivalence k).inverse.obj K).obj) := by
  unfold projectiveCoefficientNatTrans
  rfl

/-- The original quotient from the unreduced projective torus tensor. -/
def projectiveReducedTorusTensorQuotient :
    projectiveTorusTensorToDerivedMinus k ⟶ projectiveReducedTorusTensorToDerivedMinus k :=
  Functor.whiskerRight (projectiveCoefficientNatTrans k (reducedParameterTensorQuotient k))
    (nisnevichSheafify k).mapDerivedCategoryMinus

/-- The section determined by the literal torus unit and projection. -/
def projectiveReducedTorusTensorSection :
    projectiveReducedTorusTensorToDerivedMinus k ⟶ projectiveTorusTensorToDerivedMinus k :=
  Functor.whiskerRight (projectiveCoefficientNatTrans k (reducedParameterTensorSection k))
    (nisnevichSheafify k).mapDerivedCategoryMinus

/-- The original reduced quotient splits on projective representatives. -/
@[reassoc]
theorem projectiveReducedTorusTensorSection_quotient
    (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) :
    (projectiveReducedTorusTensorSection k).app K ≫
        (projectiveReducedTorusTensorQuotient k).app K = 𝟙 _ := by
  let a := (nisnevichSheafify k).mapDerivedCategoryMinus
  let s := (projectiveCoefficientNatTrans k (reducedParameterTensorSection k)).app K
  let q := (projectiveCoefficientNatTrans k (reducedParameterTensorQuotient k)).app K
  change a.map s ≫ a.map q = 𝟙 _
  rw [← a.map_comp, ← a.map_id]
  congr 1
  apply ObjectProperty.hom_ext
  let P := ((boundedAboveProjectiveEquivalence k).inverse.obj K).obj
  let S := (reducedParameterTensorSection k).mapHomotopyCategory (.up ℤ)
  let Q := (reducedParameterTensorQuotient k).mapHomotopyCategory (.up ℤ)
  change DerivedCategory.Qh.map (S.app P) ≫ DerivedCategory.Qh.map (Q.app P) = 𝟙 _
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_id]
  congr 1
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [← hL]
  change (HomotopyCategory.quotient _ _).map
        (((reducedParameterTensorSection k).mapHomologicalComplex (.up ℤ)).app L) ≫
      (HomotopyCategory.quotient _ _).map
        (((reducedParameterTensorQuotient k).mapHomologicalComplex (.up ℤ)).app L) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_id]
  congr 1
  ext n : 1
  exact reducedParameterTensorSection_quotient k (L.X n)

/-- The reduced split projector is the complement of the original
base summand on the actual projective model. -/
@[reassoc]
theorem projectiveReducedTorusTensorQuotient_section
    (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) :
    (projectiveReducedTorusTensorQuotient k).app K ≫
        (projectiveReducedTorusTensorSection k).app K =
      𝟙 _ - (Functor.whiskerRight
        (projectiveCoefficientNatTrans k
          (torusParameterTensorProjection k ≫ torusParameterTensorUnit k))
        (nisnevichSheafify k).mapDerivedCategoryMinus).app K := by
  let C := PresheafWithTransfers.{u + 1} k
  let a := (nisnevichSheafify k).mapDerivedCategoryMinus
  let s := (projectiveCoefficientNatTrans k (reducedParameterTensorSection k)).app K
  let q := (projectiveCoefficientNatTrans k (reducedParameterTensorQuotient k)).app K
  let i := torusParameterTensorUnit k
  let r := torusParameterTensorProjection k
  let p := (projectiveCoefficientNatTrans k (r ≫ i)).app K
  let X := (projectiveDerivedMinusFunctor k (parameterTensorFunctor
    (SmoothSite.multiplicativeGroupObject (Spec (.of k))))).obj K
  change a.map q ≫ a.map s = 𝟙 (a.obj X) - a.map p
  have ha : a.map q ≫ a.map s = a.map (q ≫ s) := (a.map_comp q s).symm
  have hb : 𝟙 (a.obj X) - a.map p = a.map (𝟙 X - p) :=
    (congrArg (· - a.map p) (a.map_id X).symm).trans
      (a.map_sub (f := 𝟙 X) (g := p)).symm
  rw [ha, hb]
  congr 1
  apply ObjectProperty.hom_ext
  let P := ((boundedAboveProjectiveEquivalence k).inverse.obj K).obj
  let c := ComplexShape.up ℤ
  let S := (reducedParameterTensorSection k).mapHomotopyCategory c
  let Q := (reducedParameterTensorQuotient k).mapHomotopyCategory c
  let T := (r ≫ i).mapHomotopyCategory c
  let F := parameterTensorFunctor (SmoothSite.multiplicativeGroupObject (Spec (.of k)))
  let D : HomotopyCategory C c ⥤ DerivedCategory C := DerivedCategory.Qh
  have hHom (A : HomotopyCategory C c) :
      Q.app A ≫ S.app A = 𝟙 ((F.mapHomotopyCategory c).obj A) - T.app A := by
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective A
    let U := HomotopyCategory.quotient C c
    let Z := (F.mapHomologicalComplex c).obj L
    let q' := ((reducedParameterTensorQuotient k).mapHomologicalComplex c).app L
    let s' := ((reducedParameterTensorSection k).mapHomologicalComplex c).app L
    let p' := ((r ≫ i).mapHomologicalComplex c).app L
    have h : q' ≫ s' = 𝟙 Z - p' := by
      ext n : 1
      exact reducedParameterTensorQuotient_section k (L.X n)
    change U.map q' ≫ U.map s' = 𝟙 (U.obj Z) - U.map p'
    calc
      _ = U.map (q' ≫ s') := (U.map_comp q' s').symm
      _ = U.map (𝟙 Z - p') := U.congr_map h
      _ = U.map (𝟙 Z) - U.map p' := U.map_sub
      _ = _ := congrArg (· - U.map p') (U.map_id Z)
  let Z := (F.mapHomotopyCategory c).obj P
  change D.map (Q.app P) ≫ D.map (S.app P) = 𝟙 (D.obj Z) - D.map (T.app P)
  calc
    _ = D.map (Q.app P ≫ S.app P) := (D.map_comp _ _).symm
    _ = D.map (𝟙 Z - T.app P) := D.congr_map (hHom P)
    _ = D.map (𝟙 Z) - D.map (T.app P) := D.map_sub
    _ = _ := congrArg (· - D.map (T.app P)) (D.map_id Z)

end AlgebraicGeometry.SheafWithTransfers
