/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Actual tensor extension and native module localization

The tensor universal property gives the natural isomorphism between the literal
extension-of-scalars functor and Mathlib's localized-module functor. Its unit
formula retains the original localization map.

Implementation source: the general module comparison in
`Quillen/GTheory/Dedekind/LocalDvrComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, now in its common algebraic owner.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

variable {A : Type u} [CommRing A] (S : Submonoid A)

/-- The coefficient identity compares the explicit restricted and canonical scalar actions. -/
def tensorCoefficientEquiv :
    (ModuleCat.restrictScalars (algebraMap A (Localization S))).obj
        (ModuleCat.of (Localization S) (Localization S)) ≃ₗ[A] Localization S :=
  { AddEquiv.refl _ with
    map_smul' := by
      intro r s
      change (algebraMap A (Localization S) r) * (show Localization S from s) =
        r • (show Localization S from s)
      exact (Algebra.smul_def r (show Localization S from s)).symm }

/-- Scalar extension's actual coefficient action agrees with the canonical localization action. -/
def extensionTensorEquiv (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A (Localization S))).obj M ≃ₗ[Localization S]
      Localization S ⊗[A] M :=
  { (TensorProduct.congr (tensorCoefficientEquiv S) (LinearEquiv.refl A M)).toAddEquiv with
    map_smul' := by
      intro r x
      change (TensorProduct.congr (tensorCoefficientEquiv S) (LinearEquiv.refl A M))
          (r • x) = r •
        (TensorProduct.congr (tensorCoefficientEquiv S) (LinearEquiv.refl A M)) x
      refine TensorProduct.inductionOn x ?_ ?_
      · intro s m
        simp only [TensorProduct.smul_tmul', TensorProduct.congr_tmul]
        rfl
      · intro x y hx hy
        simp only [smul_add, map_add, hx, hy] }

private theorem extensionTensorEquiv_tmul (M : ModuleCat.{u} A) (s : Localization S) (m : M) :
    extensionTensorEquiv S M (s ⊗ₜ[A,algebraMap A (Localization S)] m) = s ⊗ₜ[A] m := by
  exact TensorProduct.congr_tmul _ _ _ _

/-- The tensor universal property compares the actual localized-module object. -/
def localizationTensorIsoApp (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A (Localization S))).obj M ≅ M.localizedModule S :=
  (extensionTensorEquiv S M).toModuleIso ≪≫
    (IsLocalizedModule.isBaseChange S (Localization S)
      (M.localizedModuleMkLinearMap S)).equiv.toModuleIso

private theorem localizationTensorIsoApp_unit (M : ModuleCat.{u} A) (m : M) :
    (localizationTensorIsoApp S M).hom
        ((1 : Localization S) ⊗ₜ[A,algebraMap A (Localization S)] m) =
      M.localizedModuleMkLinearMap S m := by
  dsimp only [localizationTensorIsoApp, Iso.trans_hom]
  rw [ModuleCat.comp_apply]
  change (IsLocalizedModule.isBaseChange S (Localization S)
    (M.localizedModuleMkLinearMap S)).equiv (extensionTensorEquiv S M
      ((1 : Localization S) ⊗ₜ[A,algebraMap A (Localization S)] m)) = _
  rw [extensionTensorEquiv_tmul, IsBaseChange.equiv_tmul, one_smul]

attribute [irreducible] localizationTensorIsoApp

set_option backward.isDefEq.respectTransparency true in
/-- Tensor extension and the original module-localization functor are canonically isomorphic. -/
def localizationTensorIso :
    ModuleCat.extendScalars (algebraMap A (Localization S)) ≅
      ModuleCat.localizedModuleFunctor.{u} S :=
  NatIso.ofComponents
    (F := ModuleCat.extendScalars (algebraMap A (Localization S)))
    (G := ModuleCat.localizedModuleFunctor.{u} S)
    (fun (M : ModuleCat.{u} A) => localizationTensorIsoApp S M) (by
    intro M N f
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (localizationTensorIsoApp S N).hom
        ((ModuleCat.extendScalars (algebraMap A (Localization S))).map f
          ((1 : Localization S) ⊗ₜ[A,algebraMap A (Localization S)] m)) =
      (ModuleCat.localizedModuleMap S f) ((localizationTensorIsoApp S M).hom
        ((1 : Localization S) ⊗ₜ[A,algebraMap A (Localization S)] m))
    erw [ModuleCat.ExtendScalars.map_tmul, localizationTensorIsoApp_unit,
      localizationTensorIsoApp_unit]
    exact (IsLocalizedModule.map_apply S (M.localizedModuleMkLinearMap S)
      (N.localizedModuleMkLinearMap S) f.hom m).symm)

end ModuleCat
