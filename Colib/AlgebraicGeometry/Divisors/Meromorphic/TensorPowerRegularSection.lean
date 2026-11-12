/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridgeSuccIso
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic

/-!
# Ordinary powers on the original open

The native successor comparisons form powers of an ordinary section on an unchanged open.
These constructions make no integrality or reducedness assumption.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules (schemeTensorPower)
open Stacks.SheafOfModules.Invertible

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) (L : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]

local instance regularPowerTensorEquivalence :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj L).IsEquivalence :=
  @Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL

local instance regularPowerInvertible :
    SheafOfModules.IsInvertible X.presheaf (ringSheafCond X) L := hL.toAlgebraicGeometry

local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- Natural powers of an ordinary section, using exactly the native integral tensor-power
objects and their successor comparisons. The zeroth section is one. -/
def natTensorPowerRegularSection (U : X.Opens) (s : Γ(L, U)) :
    (n : ℕ) → Γ(schemeTensorPower X L hL (n : ℤ), U)
  | 0 => (1 : Γ(X, U))
  | n + 1 => Hom.app
      (Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso X.presheaf X.ringCatIsSheaf L
        (n : ℤ)).hom U
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        (schemeTensorPower X L hL (n : ℤ)) L (natTensorPowerRegularSection U s n) s)

/-- In degree one the ordinary power is the original section transported through the
native first-power isomorphism, exactly as in the meromorphic positive-power construction. -/
theorem natTensorPowerRegularSection_one (U : X.Opens) (s : Γ(L, U)) :
    natTensorPowerRegularSection X L U s 1 =
      Hom.app (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso
        X.presheaf X.ringCatIsSheaf L).inv U s := by
  exact (Stacks.SheafOfModules.tensorSections_leftUnitorInvAt X.presheaf X.ringCatIsSheaf
    L (op U) s).symm

/-- A frame reading the original section as one reads every actual ordinary power as one,
under the exact power frame used by the finite-boundary root theorem. -/
@[colib_tag "COL-1058",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/EtaleCohomology/KummerTheory/Basic.lean:93-106,749-763"
    "ingredient" "The original Kummer power map and structure-sheaf power trivialization",
  colib_ref "axiom_stacks_5ed82d14"
    "Algebra/Category/ModuleCat/Sheaf/TensorPowerBridgeSuccIso.lean:89-104"
    "ingredient" "The two native successor comparisons agree"]
theorem tensorPowerFrame_natTensorPowerRegularSection_eq_one (U : X.Opens) (s : Γ(L, U))
    (e : L ≅ SheafOfModules.unit (ringSheaf X))
    (he : Hom.app e.hom U s = (1 : Γ(X, U))) (n : ℕ) :
    Hom.app (tensorPowerMap X e n ≪≫ structureSheafTensorPowerIso X n).hom U
      (natTensorPowerRegularSection X L U s n) = (1 : Γ(X, U)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let P := schemeTensorPower X L hL (n : ℤ)
    let O := SheafOfModules.unit (ringSheaf X)
    let SP := tensorPowerSuccIso X.presheaf (ringSheafCond X) L (n : ℤ)
    let SO := tensorPowerSuccIso X.presheaf (ringSheafCond X) O (n : ℤ)
    let E := tensorProductIso X.presheaf (ringSheafCond X) (tensorPowerMap X e n) e
    let F := tensorProductIso X.presheaf (ringSheafCond X)
      (structureSheafTensorPowerIso X n) (Iso.refl O)
    let R := tensorProductRightUnitor X.presheaf (ringSheafCond X) O
    let t : Γ(tensorObj P L, U) :=
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
      (op U) P L (natTensorPowerRegularSection X L U s n) s
    have hS : Hom.app SP.inv U (natTensorPowerRegularSection X L U s (n + 1)) = t := by
      have hstep : natTensorPowerRegularSection X L U s (n + 1) = Hom.app SP.hom U t :=
        (congrArg (fun g => Hom.app g U t)
          (tensorPowerSuccIso_hom_eq X.presheaf (ringSheafCond X) L (n : ℤ))).symm
      exact (congrArg (Hom.app SP.inv U) hstep).trans
        (Stacks.SheafOfModules.sheafIso_inv_hom_apply X.presheaf (ringSheafCond X) _ _ SP
          (op U) t)
    change Hom.app R.hom U (Hom.app F.hom U (Hom.app SO.inv U (Hom.app SO.hom U
      (Hom.app E.hom U (Hom.app SP.inv U
        (natTensorPowerRegularSection X L U s (n + 1))))))) = _
    refine (congrArg (fun z => Hom.app R.hom U (Hom.app F.hom U (Hom.app SO.inv U
      (Hom.app SO.hom U (Hom.app E.hom U z))))) hS).trans ?_
    refine (congrArg (fun z => Hom.app R.hom U (Hom.app F.hom U z))
      (Stacks.SheafOfModules.sheafIso_inv_hom_apply X.presheaf (ringSheafCond X) _ _ SO
        (op U) (Hom.app E.hom U t))).trans ?_
    refine (congrArg (fun z => Hom.app R.hom U (Hom.app F.hom U z))
      (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.presheaf (ringSheafCond X)
        (op U) _ _ _ _ (tensorPowerMap X e n) e _ s)).trans ?_
    refine (congrArg (Hom.app R.hom U)
      (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.presheaf (ringSheafCond X)
        (op U) _ _ _ _ (structureSheafTensorPowerIso X n) (Iso.refl O) _ _)).trans ?_
    refine (congrArg (fun z => Hom.app R.hom U
      (Stacks.SheafOfModules.tensorSectionsAt X.presheaf (ringSheafCond X) (op U) O O
        (Hom.app (tensorPowerMap X e n ≪≫ structureSheafTensorPowerIso X n).hom U
          (natTensorPowerRegularSection X L U s n)) z)) he).trans ?_
    exact (Stacks.SheafOfModules.tensorSections_rightUnitorAt X.presheaf (ringSheafCond X)
      (op U) O _).trans ih

end AlgebraicGeometry.Scheme.Modules
