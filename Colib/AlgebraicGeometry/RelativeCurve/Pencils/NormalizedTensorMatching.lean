/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.NormalizedBoundarySections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.TensorZeroProduct
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLeftUnitorSections

/-!
# Literal whole-boundary matching for the graph pencil

The fixed-factor numerator normalization and the scalar numerator normalization
imply equality of the two actual polynomial endpoints on the whole boundary.
All comparisons are the native tensor and pullback isomorphisms. The resulting
identity has start `canonical graph section tensor b tensor d` and end
`a tensor n`, in the same left-associated native tensor module.

This is the section-level matching used by the original
`RelativeCurve/Pencils/Data/Serre.lean` and `Moving/Pencils/DiagonalSigned.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors Opposite
open Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

variable {X : Scheme.{u}}

/-- The native tensor of two isomorphisms acts literally on product sections. -/
theorem tensorProductIso_tensorSection {M M' N N' : X.Modules}
    (e : M ≅ M') (f : N ≅ N') (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) :
    (tensorProductIso X.presheaf X.ringCatSheaf.2 e f).hom.app ⊤
      (tensorSection M N ⊤ a b) =
        tensorSection M' N' ⊤ (e.hom.app ⊤ a) (f.hom.app ⊤ b) :=
  Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.presheaf X.ringCatSheaf.2
    (op ⊤) M M' N N' e f a b

/-- Contract a first factor using its actual frame. -/
def frameTensorContraction (F T : X.Modules)
    (e : F ≅ SheafOfModules.unit X.ringCatSheaf) : tensorModules F T ≅ T :=
  tensorProductIso X.presheaf X.ringCatSheaf.2 e (Iso.refl T) ≪≫
    tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 T

/-- On a product section, contraction is multiplication by the frame coordinate. -/
theorem frameTensorContraction_tensorSection (F T : X.Modules)
    (e : F ≅ SheafOfModules.unit X.ringCatSheaf) (a : Γ(F, ⊤)) (b : Γ(T, ⊤)) :
    (frameTensorContraction F T e).hom.app ⊤ (tensorSection F T ⊤ a b) =
      e.hom.app ⊤ a • b := by
  change (tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 T).hom.app ⊤
      ((tensorProductIso X.presheaf X.ringCatSheaf.2 e (Iso.refl T)).hom.app ⊤
        (tensorSection F T ⊤ a b)) = _
  rw [tensorProductIso_tensorSection]
  exact Stacks.SheafOfModules.tensorProductLeftUnitor_hom_val_app_toTensorSheafSection
    X.toRingedSpace T (op ⊤) (e.hom.app ⊤ a) b

/-- The two actual normalizations imply the graph-times-poles endpoint identity. -/
theorem tensorSection_matching_of_normalizations (F T N : X.Modules)
    (e : F ≅ SheafOfModules.unit X.ringCatSheaf)
    (σ : Γ(F, ⊤)) (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤))
    (n d : Γ(N, ⊤))
    (ha : (frameTensorContraction F T e).hom.app ⊤ a = b)
    (hn : n = e.hom.app ⊤ σ • d) :
    tensorSection (tensorModules F T) N ⊤ a n =
      tensorSection (tensorModules F T) N ⊤ (tensorSection F T ⊤ σ b) d := by
  have hσ : tensorSection F T ⊤ σ b = e.hom.app ⊤ σ • a := by
    apply (ConcreteCategory.bijective_of_isIso
      ((frameTensorContraction F T e).hom.app ⊤)).injective
    rw [frameTensorContraction_tensorSection, Modules.Hom.app_smul, ha]
  rw [hn, tensorSection_smul_right, hσ, tensorSection_smul_left]

/-- Pullback of a tensor section, at the same native module spelling as its zero ideal. -/
theorem pullbackTensorIso_tensorSection {Z : Scheme.{u}} (i : Z ⟶ X)
    (M N : X.Modules) (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) :
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i M N).hom.app ⊤
      (pullbackGlobalSections i _ (tensorSection M N ⊤ a b)) =
        tensorSection ((Modules.pullback i).obj M) ((Modules.pullback i).obj N) ⊤
          (pullbackGlobalSections i M a) (pullbackGlobalSections i N b) :=
  Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt i M N a b

/-- The literal comparison for the left-associated three-factor tensor product. -/
def nestedPullbackTensorIso {Z : Scheme.{u}} (i : Z ⟶ X) (F T N : X.Modules) :
    (Modules.pullback i).obj (tensorModules (tensorModules F T) N) ≅
      tensorModules (tensorModules ((Modules.pullback i).obj F) ((Modules.pullback i).obj T))
        ((Modules.pullback i).obj N) :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i (tensorModules F T) N ≪≫
    tensorProductIso Z.presheaf Z.ringCatSheaf.2
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i F T) (Iso.refl _)

/-- Its value on the actual numerator product, retaining the fixed-factor comparison. -/
theorem nestedPullbackTensorIso_product {Z : Scheme.{u}} (i : Z ⟶ X)
    (F T N : X.Modules) (a : Γ(tensorModules F T, ⊤)) (n : Γ(N, ⊤)) :
    (nestedPullbackTensorIso i F T N).hom.app ⊤
      (pullbackGlobalSections i _ (tensorSection (tensorModules F T) N ⊤ a n)) =
        tensorSection (tensorModules ((Modules.pullback i).obj F) ((Modules.pullback i).obj T))
          ((Modules.pullback i).obj N) ⊤
          ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i F T).hom.app ⊤
            (pullbackGlobalSections i _ a)) (pullbackGlobalSections i _ n) := by
  change (tensorProductIso Z.presheaf Z.ringCatSheaf.2
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i F T) (Iso.refl _)).hom.app ⊤
    ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i (tensorModules F T) N).hom.app ⊤
      (pullbackGlobalSections i _ (tensorSection (tensorModules F T) N ⊤ a n))) = _
  rw [pullbackTensorIso_tensorSection, tensorProductIso_tensorSection]
  rfl

/-- The two actually prescribed normalized pairs match on the whole original
boundary, so the polynomial family is constant there. The conclusion is equality
of sections before passing to zero schemes or correspondences. -/
theorem boundary_tensorSection_matching {Z : Scheme.{u}} (i : Z ⟶ X)
    (F T N : X.Modules)
    (eF : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf)
    (σ : Γ(F, ⊤)) (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤)) (n d : Γ(N, ⊤))
    (ha : (fixedFactorBoundaryIso i F T eF).hom.app ⊤
      (pullbackGlobalSections i _ a) = pullbackGlobalSections i _ b)
    (hn : pullbackGlobalSections i _ n =
      eF.hom.app ⊤ (pullbackGlobalSections i F σ) • pullbackGlobalSections i _ d) :
    pullbackGlobalSections i _ (tensorSection (tensorModules F T) N ⊤ a n) =
      pullbackGlobalSections i _
        (tensorSection (tensorModules F T) N ⊤ (tensorSection F T ⊤ σ b) d) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((nestedPullbackTensorIso i F T N).hom.app ⊤)).injective
  rw [nestedPullbackTensorIso_product, nestedPullbackTensorIso_product,
    pullbackTensorIso_tensorSection]
  apply tensorSection_matching_of_normalizations _ _ _ eF
    (pullbackGlobalSections i F σ) _ (pullbackGlobalSections i T b)
    (pullbackGlobalSections i N n) (pullbackGlobalSections i N d) _ hn
  exact ha

end AlgebraicGeometry.Scheme.RelativeCurvePencil
