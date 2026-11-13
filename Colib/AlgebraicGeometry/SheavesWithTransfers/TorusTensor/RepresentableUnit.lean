/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Unit
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Sheafification
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction

/-!
# The projective torus tensor transpose of the original exterior map

A transfer representable in degree zero is a bounded-above projective
complex. Tensoring this representative and projecting to the original
target unit quotient transposes to the actual signed exterior product,
followed by the coefficient sheafification unit. The same formula
holds after the original target singular augmentation and localization.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u w₁ w₂

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "c" => ComplexShape.up ℤ
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "F" => Cor.parameterProduct Gₘ
local notation "A" => nisnevichSheafify k
local notation "U" => (SheafWithTransfers.forget k : NST ⥤ PST)
local notation "L" => parameterTensorFunctor Gₘ ⋙ A
local notation "R" => U ⋙ (withParameterFunctor Gₘ : PST ⥤ PST)
local notation "sₚ" => HomologicalComplex.single PST c (0 : ℤ)
local notation "sₛ" => HomologicalComplex.single NST c (0 : ℤ)
set_option quotPrecheck false in
local notation "r(" Y ")" => (representableLarge k).obj Y
local notation "C(" Y ")" => torusCancellationCoefficients k Y

/-- The actual representable in degree zero is an object of the projective model. -/
def projectiveRepresentableSingle (Y : Cor k) : BoundedAboveProjectiveHomotopy k := by
  let K : CochainComplex PST ℤ := (sₚ).obj (r(Y))
  refine ⟨(HomotopyCategory.quotient PST c).obj K, 0, ?_, ?_⟩
  · exact inferInstanceAs (CochainComplex.IsStrictlyLE ((sₚ).obj (r(Y))) 0)
  · intro i
    by_cases hi : i = 0
    · subst i
      change Projective (((sₚ).obj (r(Y))).X 0)
      rw [HomologicalComplex.single_obj_X_self]
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X c 0 (r(Y)) i hi).projective

/-- The target unit quotient of the original tensor on a representable. -/
def torusTensorRepresentableQuotient (Y : Cor k) :
    (L).obj (r(Y)) ⟶ (A).obj (C(Y)) :=
  (A).map ((parameterTensorRepresentableIso Gₘ Y).hom ≫ toTorusCancellationCoefficients k Y)

/-- The adjunction transpose is the original signed exterior product followed
by its target quotient and the actual coefficient sheafification unit. -/
theorem torusTensorRepresentableQuotient_homEquiv (Y : Cor k) :
    ((parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k)).homEquiv
      (r(Y)) ((A).obj (C(Y))) (torusTensorRepresentableQuotient k Y) =
    torusCancellationParameterMap k Y ≫
      (withParameterFunctor Gₘ : PST ⥤ PST).map (toNisnevichSheafify k (C(Y))) := by
  let t := parameterTensorAdjunction Gₘ
  let a := nisnevichSheafificationAdjunction k
  let E : PST ⥤ PST := withParameterFunctor Gₘ
  let e := (parameterTensorRepresentableIso Gₘ Y).hom
  let q := toTorusCancellationCoefficients k Y
  have he : (t.homEquiv _ _) e = torusExteriorRepresentableMap k Y := by
    rw [Adjunction.homEquiv_unit]
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨b⟩ := z
    change e.hom.app (op ((F).obj X.unop))
        ((t.unit.app (r(Y))).hom.app X (ULift.up b)) =
      ULift.up ((F).map b)
    exact parameterTensorRepresentable_unit_app Gₘ Y X.unop b
  change (t.comp a).homEquiv _ _ ((A).map (e ≫ q)) = _
  rw [Adjunction.comp_homEquiv]
  change (t.homEquiv _ _) ((a.homEquiv _ _) ((A).map (e ≫ q))) = _
  have hη : (a.homEquiv _ _) ((A).map (e ≫ q)) =
      (e ≫ q) ≫ toNisnevichSheafify k (C(Y)) := by
    have hid : (a.homEquiv _ _) (𝟙 ((A).obj (C(Y)))) = toNisnevichSheafify k (C(Y)) := by
      rw [Adjunction.homEquiv_unit, (U).map_id]
      exact (Category.comp_id (a.unit.app (C(Y)))).trans
        (nisnevichSheafificationAdjunction_unit_app k (C(Y)))
    calc
      _ = (a.homEquiv _ _) ((A).map (e ≫ q) ≫ 𝟙 _) :=
        congrArg (a.homEquiv _ _) (Category.comp_id _).symm
      _ = (e ≫ q) ≫ (a.homEquiv _ _) (𝟙 _) := a.homEquiv_naturality_left _ _
      _ = _ := congrArg ((e ≫ q) ≫ ·) hid
  rw [hη, Category.assoc, Adjunction.homEquiv_naturality_right, E.map_comp, he]
  exact (Category.assoc _ _ _).symm

/-- The actual target quotient after forming the single cochain complex. -/
def torusTensorRepresentableSingleQuotient (Y : Cor k) :
    ((L).mapHomologicalComplex c).obj ((sₚ).obj (r(Y))) ⟶ (sₛ).obj ((A).obj (C(Y))) :=
  (HomologicalComplex.singleMapHomologicalComplex (L) c (0 : ℤ)).hom.app (r(Y)) ≫
    (sₛ).map (torusTensorRepresentableQuotient k Y)

/-- The cochain transpose of the target quotient is the single of the
original exterior map and coefficient sheafification, with the native
single-complex comparison. -/
theorem torusTensorRepresentableSingleQuotient_homEquiv
    (Y : Cor k) (I : CochainComplex NST ℤ)
    (f : (sₛ).obj ((A).obj (C(Y))) ⟶ I) :
    (torusTensorCochainAdjunction k).homEquiv ((sₚ).obj (r(Y))) I
      (torusTensorRepresentableSingleQuotient k Y ≫ f) =
    (sₚ).map (torusCancellationParameterMap k Y ≫
      (withParameterFunctor Gₘ : PST ⥤ PST).map (toNisnevichSheafify k (C(Y)))) ≫
      (HomologicalComplex.singleMapHomologicalComplex (R) c (0 : ℤ)).inv.app ((A).obj (C(Y))) ≫
      ((R).mapHomologicalComplex c).map f := by
  let adj := (parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k)
  let a := torusTensorCochainAdjunction k
  let e := HomologicalComplex.singleMapHomologicalComplex (L) c (0 : ℤ)
  let d := HomologicalComplex.singleMapHomologicalComplex (R) c (0 : ℤ)
  let K := (sₚ).obj (r(Y))
  let q := torusTensorRepresentableQuotient k Y
  have h := Adjunction.mapHomologicalComplexAdjunction_unit_app_single adj c (0 : ℤ) (r(Y))
  have hu : a.unit.app K ≫ ((R).mapHomologicalComplex c).map (e.hom.app (r(Y))) =
      (sₚ).map (adj.unit.app (r(Y))) ≫ d.inv.app ((L).obj (r(Y))) := by
    let D := d.app ((L).obj (r(Y)))
    calc
      _ = (a.unit.app K ≫ ((R).mapHomologicalComplex c).map (e.hom.app (r(Y)))) ≫
          (D.hom ≫ D.inv) := by
        rw [D.hom_inv_id]
        exact (Category.comp_id _).symm
      _ = (sₚ).map (adj.unit.app (r(Y))) ≫ D.inv :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.inv)
          ((Category.assoc _ _ _).trans h))
      _ = _ := rfl
  have hv := torusTensorRepresentableQuotient_homEquiv k Y
  rw [Adjunction.homEquiv_unit] at hv
  let V := (R).mapHomologicalComplex c
  let η := (sₚ).map (adj.unit.app (r(Y)))
  let δ := d.inv.app ((A).obj (C(Y)))
  have hq : d.inv.app ((L).obj (r(Y))) ≫ V.map ((sₛ).map q) =
      (sₚ).map ((R).map q) ≫ δ := (d.inv.naturality q).symm
  calc
    _ = a.unit.app K ≫ V.map (torusTensorRepresentableSingleQuotient k Y ≫ f) :=
      a.homEquiv_unit K I _
    _ = (a.unit.app K ≫ V.map (e.hom.app (r(Y)))) ≫ V.map ((sₛ).map q) ≫ V.map f := by
      change a.unit.app K ≫ V.map ((e.hom.app (r(Y)) ≫ (sₛ).map q) ≫ f) = _
      simp only [V.map_comp, Category.assoc]
    _ = (η ≫ d.inv.app ((L).obj (r(Y)))) ≫ V.map ((sₛ).map q) ≫ V.map f :=
      congrArg (· ≫ V.map ((sₛ).map q) ≫ V.map f) hu
    _ = η ≫ (d.inv.app ((L).obj (r(Y))) ≫ V.map ((sₛ).map q)) ≫ V.map f := by
      simp only [Category.assoc]
    _ = η ≫ (sₚ).map ((R).map q) ≫ δ ≫ V.map f :=
      (congrArg (fun x => η ≫ x ≫ V.map f) hq).trans
        (congrArg (η ≫ ·) (Category.assoc _ _ _))
    _ = (sₚ).map (adj.unit.app (r(Y)) ≫ (R).map q) ≫ δ ≫ V.map f := by
      simp only [Functor.map_comp, Category.assoc, η]
    _ = _ := congrArg (fun g => (sₚ).map g ≫ δ ≫ V.map f) hv

variable [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
variable [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]

/-- The original single-to-singular augmentation of the target quotient. -/
def torusTensorRepresentableTargetAugmentation (Y : Cor k) :
    (sₛ).obj ((A).obj (C(Y))) ⟶ singularSheafCochainComplex k (C(Y)) 0 :=
  (HomologicalComplex.singleMapHomologicalComplex (A) c (0 : ℤ)).inv.app (C(Y)) ≫
    ((A).mapHomologicalComplex c).map (singularCochainUnitApp (C(Y)))

/-- On a K-injective target, the original exterior map followed by the target
augmentation is the localized projective transpose of the actual quotient. -/
theorem torusTensorRepresentableDerivedTranspose
    (Y : Cor k) (I : CochainComplex NST ℤ) [hI : CochainComplex.IsKInjective I]
    (f : singularSheafCochainComplex k (C(Y)) 0 ⟶ I) :
    let J : TorusTensorInjectiveHomotopy k := ⟨(HomotopyCategory.quotient NST c).obj I, hI⟩
    let h := torusTensorRepresentableTargetAugmentation k Y ≫ f
    torusTensorHomEquivOnRepresentatives k (projectiveRepresentableSingle k Y) J
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient NST c).map
        (torusTensorRepresentableSingleQuotient k Y ≫ h))) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient PST c).map
      ((sₚ).map (torusCancellationParameterMap k Y ≫
        (withParameterFunctor Gₘ : PST ⥤ PST).map (toNisnevichSheafify k (C(Y)))) ≫
        (HomologicalComplex.singleMapHomologicalComplex (R) c (0 : ℤ)).inv.app ((A).obj (C(Y))) ≫
        ((R).mapHomologicalComplex c).map h)) ≫
      (torusTensorInjectiveReindexingIso k).hom.app J := by
  intro J h
  rw [projectiveTorusTensor_homotopyHomEquiv_map]
  exact congrArg
    (fun g => DerivedCategory.Qh.map ((HomotopyCategory.quotient PST c).map g) ≫
      (torusTensorInjectiveReindexingIso k).hom.app J)
    (torusTensorRepresentableSingleQuotient_homEquiv k Y I h)

end AlgebraicGeometry.SheafWithTransfers
