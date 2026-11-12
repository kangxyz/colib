/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryPowerFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.CompatibleBoundaryFrames

/-! # The complete same-root and auxiliary-pair output

This named proposition is exactly the original existential output: the root,
its prescribed full-boundary power equation, an auxiliary invertible module,
two nonzero global sections and their two literal boundary-one equations.
Naming this conclusion does not supply any compatibility as an assumption.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.SheafOfModules.Invertible
universe u
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance outputRootRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance outputRootPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance outputRootUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- The complete original output, with no witness or equation omitted. -/
def FullBoundaryRootAuxiliaryOutput {X Z : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules)
    (τ : (pullback i).obj L ≅ SheafOfModules.unit Z.ringCatSheaf) (n : ℕ) : Prop :=
    ∃ (M : X.Modules)
      (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      let _ := hM
      let _ : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property M := hM.toAlgebraicGeometry
      ∃ (α : tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property M (n : ℤ) ≅
          L)
        (e : (Scheme.Modules.pullback i).obj M ≅
          _root_.SheafOfModules.unit Z.ringCatSheaf),
        tensorPowerCongr Z.presheaf (ringSheafCond Z) _ _ e n =
          boundaryRootPowerIso i M _ n α
            τ ∧
        ∃ (Naux : X.Modules)
          (_hNaux : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
            X.ringCatSheaf.property Naux)
          (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj Naux, ⊤))
          (bN : Γ(Naux, ⊤))
          (eN : (Scheme.Modules.pullback i).obj Naux ≅
            _root_.SheafOfModules.unit Z.ringCatSheaf),
          a ≠ 0 ∧ bN ≠ 0 ∧
          Scheme.Modules.Hom.app (X := Z)
            (Scheme.Modules.pullbackTensorFrame i M Naux e eN).hom ⊤
            (pullbackGlobalSections i _ a) = (1 : Γ(Z, ⊤)) ∧
          Scheme.Modules.Hom.app (X := Z) eN.hom ⊤ (pullbackGlobalSections i Naux bN) =
            (1 : Γ(Z, ⊤))

end Stacks.AlgebraicGeometry.ModuleLimits
