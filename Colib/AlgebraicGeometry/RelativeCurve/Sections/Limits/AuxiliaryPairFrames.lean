/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.CompatibleBoundaryFrames
public import Colib.AlgebraicGeometry.Modules.Invertible.PullbackPowerComparison
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.CanonicalSections

/-! # Original auxiliary frames linearize the numerator boundary equation

Only the auxiliary frame is used to contract the second tensor factor. The root
frame remains an independent variable, so its original full-boundary equation
is a linear equation for the final simultaneous root-frame descent.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible
universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Contract only the auxiliary factor using its specified full-boundary frame. -/
def pullbackTensorAuxiliaryFrame {X B : Scheme.{u}} (i : B ⟶ X) (L N : X.Modules)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    (pullback i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj N) ≅
      (pullback i).obj L :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i L N ≪≫
    tensorProductIso B.sheaf.obj B.ringCatSheaf.property (Iso.refl _) eN ≪≫
      tensorProductRightUnitor B.sheaf.obj B.ringCatSheaf.property _

private theorem tensor_unit_linear {C : Type*} [Category C] [MonoidalCategory C]
    {A B : C} (e : A ⟶ 𝟙_ C) (n : B ⟶ 𝟙_ C) :
    (𝟙 A ⊗ₘ n) ≫ (ρ_ A).hom ≫ e = (e ⊗ₘ n) ≫ (λ_ (𝟙_ C)).hom := by
  rw [← MonoidalCategory.rightUnitor_naturality, MonoidalCategory.unitors_equal,
    MonoidalCategory.id_tensorHom, ← Category.assoc, ← MonoidalCategory.tensorHom_def']

/-- The actual product frame factors through the auxiliary contraction and the
original root frame. Both sides are full module morphisms on the whole boundary. -/
theorem pullbackTensorAuxiliaryFrame_trans {X B : Scheme.{u}} (i : B ⟶ X)
    (L N : X.Modules)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    pullbackTensorAuxiliaryFrame i L N eN ≪≫ e = pullbackTensorFrame i L N e eN := by
  let : MonoidalCategory B.Modules :=
    Stacks.PullbackGradedAlgebra.monoidalCategory B.toRingedSpace
  have h := tensor_unit_linear e.hom eN.hom
  have hr := Stacks.SheafOfModules.Strict_rightUnitor_eq B.presheaf B.ringCatIsSheaf
    ((pullback i).obj L)
  have hl := Stacks.SheafOfModules.Strict_leftUnitor_eq B.presheaf B.ringCatIsSheaf
    (SheafOfModules.unit B.ringCatSheaf)
  have ht₁ := Stacks.SheafOfModules.tensorSheafMapIso_hom_eq B.presheaf B.ringCatIsSheaf
    (Iso.refl ((pullback i).obj L)) eN
  have ht₂ := Stacks.SheafOfModules.tensorSheafMapIso_hom_eq B.presheaf B.ringCatIsSheaf e eN
  apply Iso.ext
  change (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i L N).hom ≫
    (tensorProductIso B.sheaf.obj B.ringCatSheaf.property (Iso.refl _) eN).hom ≫
    (tensorProductRightUnitor B.sheaf.obj B.ringCatSheaf.property _).hom ≫ e.hom =
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i L N).hom ≫
    (tensorProductIso B.sheaf.obj B.ringCatSheaf.property e eN).hom ≫
    (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property _).hom
  congr 1
  have hr' : (tensorProductRightUnitor B.sheaf.obj B.ringCatSheaf.property
      ((pullback i).obj L)).hom = (ρ_ ((pullback i).obj L)).hom :=
    (congrArg Iso.hom hr).symm
  have hl' : (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
      (SheafOfModules.unit B.ringCatSheaf)).hom = (λ_ (𝟙_ B.Modules)).hom :=
    (congrArg Iso.hom hl).symm
  have ht₁' : (tensorProductIso B.sheaf.obj B.ringCatSheaf.property
      (Iso.refl ((pullback i).obj L)) eN).hom = 𝟙 ((pullback i).obj L) ⊗ₘ eN.hom := ht₁
  have ht₂' : (tensorProductIso B.sheaf.obj B.ringCatSheaf.property e eN).hom =
      e.hom ⊗ₘ eN.hom := ht₂
  exact (congrArg₂ (fun a b => a ≫ b ≫ e.hom) ht₁' hr').trans
    (h.trans (congrArg₂ (fun a b => a ≫ b) ht₂' hl').symm)

/-- The original scalar normalization is precisely an equation of morphisms out
of the structure sheaf, suitable for native finite linear-equation descent. -/
theorem unitHomEquivTop_comp_eq_iff {B : Scheme.{u}} {M N : B.Modules}
    (θ : M ⟶ N) (x : Γ(M, ⊤)) (y : Γ(N, ⊤)) :
    unitHomEquivTop M x ≫ θ = unitHomEquivTop N y ↔ Hom.app θ ⊤ x = y := by
  have h : unitHomEquivTop N (Hom.app θ ⊤ x) = unitHomEquivTop M x ≫ θ := by
    apply (SheafOfModules.unitHomEquiv N).injective
    refine (unitHomEquiv_unitHomEquivTop N _).trans ?_
    refine Eq.trans ?_ (SheafOfModules.unitHomEquiv_comp_apply
      (unitHomEquivTop M x) θ).symm
    refine Eq.trans ?_ (congrArg (SheafOfModules.sectionsMap θ)
      (unitHomEquiv_unitHomEquivTop M x)).symm
    ext U
    simp only [sectionsTopEquiv_val, sectionsMap_val]
    exact (PresheafOfModules.naturality_apply θ.val
      (homOfLE (show U.unop ≤ ⊤ from le_top)).op x).symm
  rw [← h]
  exact (unitHomEquivTop N).injective.eq_iff

/-- The numerator gives a concrete linear section into the boundary root module.
Its definition uses only the auxiliary frame, never the unknown root frame. -/
def auxiliaryBoundaryNumerator {X B : Scheme.{u}} (i : B ⟶ X) (L N : X.Modules)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj N, ⊤)) :
    Scheme.unitModule B ⟶ (pullback i).obj L :=
  unitHomEquivTop _ (pullbackGlobalSections i _ a) ≫
    (pullbackTensorAuxiliaryFrame i L N eN).hom

/-- Original full-boundary numerator normalization equals the concrete linear
frame equation. The right side retains the actual boundary value one. -/
theorem auxiliaryBoundaryNumerator_frame_eq_iff {X B : Scheme.{u}} (i : B ⟶ X)
    (L N : X.Modules)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj N, ⊤)) :
    auxiliaryBoundaryNumerator i L N eN a ≫ e.hom =
      unitHomEquivTop (SheafOfModules.unit B.ringCatSheaf) (1 : Γ(B, ⊤)) ↔
    Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i _ a) = (1 : Γ(B, ⊤)) := by
  have h := congrArg Iso.hom (pullbackTensorAuxiliaryFrame_trans i L N e eN)
  change (pullbackTensorAuxiliaryFrame i L N eN).hom ≫ e.hom =
    (pullbackTensorFrame i L N e eN).hom at h
  change (unitHomEquivTop _ (pullbackGlobalSections i _ a) ≫
    (pullbackTensorAuxiliaryFrame i L N eN).hom) ≫ e.hom = _ ↔ _
  have hc := (Category.assoc
    (unitHomEquivTop _ (pullbackGlobalSections i _ a))
    (pullbackTensorAuxiliaryFrame i L N eN).hom e.hom).trans
      (congrArg (fun m => unitHomEquivTop _ (pullbackGlobalSections i _ a) ≫ m) h)
  exact (Iff.of_eq (congrArg (fun m => m =
    unitHomEquivTop (SheafOfModules.unit B.ringCatSheaf) (1 : Γ(B, ⊤))) hc)).trans
      (unitHomEquivTop_comp_eq_iff _ _ _)

end AlgebraicGeometry.Scheme.Modules
