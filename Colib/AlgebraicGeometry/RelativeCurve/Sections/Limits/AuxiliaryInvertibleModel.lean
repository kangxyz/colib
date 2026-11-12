/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.LimitRoot
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.CanonicalSections

/-! # Actual auxiliary invertible module at a refinement of the fixed root stage

The native invertible-module descent is applied over the specified root stage.
The root model is only pulled back, never reselected. Both original module
identifications determine the actual tensor comparison for the numerator.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
universe u
namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- Original root and auxiliary identifications give the actual numerator tensor
identification. It is built from the native canonical comparisons. -/
def auxiliaryTensorModelIso {W X Y : Scheme.{u}} (q : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : q ≫ g = p) (L : Y.Modules) (N : X.Modules)
    (M A : W.Modules) (eM : M ≅ (Scheme.Modules.pullback p).obj L)
    (eA : A ≅ (Scheme.Modules.pullback q).obj N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor W.sheaf).obj M).obj A ≅
      (Scheme.Modules.pullback q).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          ((Scheme.Modules.pullback g).obj L)).obj N) :=
  tensorProductIso W.sheaf.obj W.ringCatSheaf.property
    (eM ≪≫ (canIso q g p hp L).symm) eA ≪≫
      (pullbackTensorIso q ((Scheme.Modules.pullback g).obj L) N).symm

/-- Descend the original auxiliary invertible module after a fixed original root
stage, retaining its actual identification and the original numerator tensor.
No auxiliary module at a stage is assumed, and the root model is unchanged. -/
theorem exists_auxiliaryInvertible_tensorModel_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (L : (D.obj i).Modules) (M N : c.pt.Modules)
    (eM : M ≅ (Scheme.Modules.pullback (c.π.app i)).obj L)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible
      c.pt.sheaf.obj c.pt.ringCatSheaf.property N) :
    ∃ (j : I) (f : j ⟶ i) (Nj : (D.obj j).Modules)
      (_hNj : AlgebraicGeometry.SheafOfModules.IsInvertible
        (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property Nj)
      (_eN : N ≅ (Scheme.Modules.pullback (c.π.app j)).obj Nj),
      Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N ≅
        (Scheme.Modules.pullback (c.π.app j)).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor (D.obj j).sheaf).obj
            ((Scheme.Modules.pullback (D.map f)).obj L)).obj Nj)) := by
  have hc' : IsLimit (c.whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have : ∀ {j k : Over i} (f : j ⟶ k), IsAffineHom ((Over.forget i ⋙ D).map f) :=
    fun f => inferInstanceAs (IsAffineHom (D.map f.left))
  have : ∀ j : Over i, CompactSpace ((Over.forget i ⋙ D).obj j) :=
    fun j => inferInstanceAs (CompactSpace (D.obj j.left))
  have : ∀ j : Over i, QuasiSeparatedSpace ((Over.forget i ⋙ D).obj j) :=
    fun j => inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  obtain ⟨j, Nj, hNj, ⟨eN⟩⟩ := exists_isInvertible_pullback_iso_of_isLimit
    (Over.forget i ⋙ D) (c.whisker (Over.forget i)) hc' N hN
  change N ≅ (Scheme.Modules.pullback (c.π.app j.left)).obj Nj at eN
  exact ⟨j.left, j.hom, Nj, hNj, eN,
    ⟨auxiliaryTensorModelIso (c.π.app j.left) (D.map j.hom) (c.π.app i)
      (c.w j.hom) L Nj M N eM eN⟩⟩

end Stacks.AlgebraicGeometry.ModuleLimits
