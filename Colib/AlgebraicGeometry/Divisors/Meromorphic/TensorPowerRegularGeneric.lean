/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRegularSection
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRatio
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.GlobalSectionTransport

/-!
# The ordinary power represents the original meromorphic power

Integrality is used only in the generic-stalk comparison, not in ordinary powers or their
full-boundary frames.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules (schemeTensorPower)

universe u

namespace AlgebraicGeometry

open Scheme.Modules

variable (X : Scheme.{u}) [IsIntegral X] (L : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]

local instance positiveRegularGenericInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  hL.toAlgebraicGeometry

local instance positiveRegularGenericTensorEquivalence :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj L).IsEquivalence :=
  @Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL

local instance positiveRegularGenericPowerInvertible (n : ℤ) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (schemeTensorPower X L hL n) :=
  (Stacks.SheafOfModules.isInvertible_schemeTensorPower X L hL n).toAlgebraicGeometry

local instance positiveRegularGenericQuasicoherent (F : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F] : F.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible F

local instance positiveRegularGenericPowerQuasicoherent (n : ℤ) :
    (schemeTensorPower X L hL n).IsQuasicoherent :=
  isQuasicoherent_of_isInvertible (show X.Modules from schemeTensorPower X L hL n)

local instance positiveRegularGenericTensorInvertible (M N : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorObj M N) := by
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M)
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (inferInstance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N)
  exact (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    M N).toAlgebraicGeometry

/-- Ordinary powers on the original open represent the very same positive meromorphic
powers used in the signed divisor correction, with their exact native comparisons. -/
@[colib_tag "COL-1058"]
theorem meromorphicGenericValue_positiveTensorPower_eq_germ_natTensorPowerRegularSection
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    (U : X.Opens) (hU : genericPoint X ∈ U) (m : Γ(L, U))
    (hm : meromorphicGenericValue X L s = L.presheaf.germ U (genericPoint X) hU m)
    (k : ℕ) :
    meromorphicGenericValue X (show X.Modules from schemeTensorPower X L hL (k + 1))
      (positiveTensorPowerMeromorphicSection X L s hs k).val =
      (show X.Modules from schemeTensorPower X L hL (k + 1)).presheaf.germ U (genericPoint X) hU
        (natTensorPowerRegularSection X L U m (k + 1)) := by
  induction k with
  | zero =>
    refine (meromorphicGenericValue_mapMeromorphicSection L
      (show X.Modules from schemeTensorPower X L hL 1)
      (schemeTensorPowerOneIso X L).inv s).trans ?_
    refine (congrArg (stalkLinearMap L (show X.Modules from schemeTensorPower X L hL 1)
      (schemeTensorPowerOneIso X L).inv (genericPoint X)) hm).trans ?_
    refine (stalkLinearMap_germ L (show X.Modules from schemeTensorPower X L hL 1)
      (schemeTensorPowerOneIso X L).inv U (genericPoint X) hU m).trans ?_
    exact congrArg ((show X.Modules from schemeTensorPower X L hL 1).presheaf.germ U
      (genericPoint X) hU)
      (natTensorPowerRegularSection_one X L U m).symm
  | succ k ih =>
    let P : X.Modules := schemeTensorPower X L hL (k + 1)
    let t : Γ(tensorObj P L, U) :=
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        P L (natTensorPowerRegularSection X L U m (k + 1)) m
    have ht : meromorphicGenericValue X (tensorObj P L)
        (tensorMeromorphicSection X P L
          (positiveTensorPowerMeromorphicSection X L s hs k).val s) =
        (tensorObj P L).presheaf.germ U (genericPoint X) hU t := by
      refine (meromorphicGenericValue_tensorMeromorphicSection X P L _ s).trans ?_
      refine (congrArg₂ (tensorStalkTmul P L (genericPoint X)) ih hm).trans ?_
      exact tensorStalkTmul_germ P L (genericPoint X) U hU _ m
    refine (meromorphicGenericValue_mapMeromorphicSection (tensorObj P L)
      (show X.Modules from schemeTensorPower X L hL (k + 1 + 1))
      (schemeTensorPowerSuccIso X L k).hom _).trans ?_
    refine (congrArg (stalkLinearMap (tensorObj P L)
      (show X.Modules from schemeTensorPower X L hL (k + 1 + 1))
      (schemeTensorPowerSuccIso X L k).hom (genericPoint X)) ht).trans ?_
    exact stalkLinearMap_germ (tensorObj P L)
      (show X.Modules from schemeTensorPower X L hL (k + 1 + 1))
      (schemeTensorPowerSuccIso X L k).hom U (genericPoint X) hU t

/-- Applying the original root isomorphism preserves the exact ordinary representative
of its positive meromorphic power. -/
@[colib_tag "COL-1058"]
theorem meromorphicGenericValue_rootImage_eq_germ_natTensorPowerRegularSection
    (P : X.Modules) [P.IsQuasicoherent]
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    (U : X.Opens) (hU : genericPoint X ∈ U) (m : Γ(L, U))
    (hm : meromorphicGenericValue X L s = L.presheaf.germ U (genericPoint X) hU m)
    (k : ℕ) (α : schemeTensorPower X L hL (k + 1) ≅ P) :
    meromorphicGenericValue X P
      (mapMeromorphicSection (show X.Modules from schemeTensorPower X L hL (k + 1)) P
        α.hom (positiveTensorPowerMeromorphicSection X L s hs k).val) =
      P.presheaf.germ U (genericPoint X) hU
        (Hom.app α.hom U (natTensorPowerRegularSection X L U m (k + 1))) := by
  refine (meromorphicGenericValue_mapMeromorphicSection
    (show X.Modules from schemeTensorPower X L hL (k + 1)) P α.hom _).trans ?_
  refine (congrArg (stalkLinearMap
    (show X.Modules from schemeTensorPower X L hL (k + 1)) P α.hom (genericPoint X))
    (meromorphicGenericValue_positiveTensorPower_eq_germ_natTensorPowerRegularSection
      X L s hs U hU m hm k)).trans ?_
  exact stalkLinearMap_germ (show X.Modules from schemeTensorPower X L hL (k + 1)) P
    α.hom U (genericPoint X) hU _

end AlgebraicGeometry
