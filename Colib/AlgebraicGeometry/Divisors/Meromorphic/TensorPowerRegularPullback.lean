/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRegularSection
public import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRoot
public import StacksFrontier.AlgebraicGeometry.Divisors.PullbackTensorTrivialization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapSuccessor

/-!
# Ordinary powers commute with the original integer pullback comparison

The comparison is exactly the one used by the root's full-boundary frame equation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules (schemeTensorPower)
open Stacks.SheafOfModules.Invertible

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- Naturality of actual section pullback on an entire inverse-image open. -/
theorem pullbackSectionHom_naturality_preimage {X B : Scheme.{u}} (i : B ⟶ X)
    {L N : X.Modules} (f : L ⟶ N) (U : X.Opens) (s : Γ(L, U)) :
    Hom.app ((pullback i).map f) (i ⁻¹ᵁ U)
      (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl s) =
    pullbackSectionHom i N U (i ⁻¹ᵁ U) le_rfl (Hom.app f U s) := by
  refine (congrArg (Hom.app ((pullback i).map f) (i ⁻¹ᵁ U))
    (pullbackSectionHom_preimage_self i L U s)).trans ?_
  exact (Stacks.RingedSpace.pullbackUnit_naturality i.toLRSHom.toShHom f (op U) s).trans
    (pullbackSectionHom_preimage_self i N U (Hom.app f U s)).symm

variable {X B : Scheme.{u}} (i : B ⟶ X) (L : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]

local instance regularPowerPullbackInvertible :
    Stacks.SheafOfModules.IsInvertible B.presheaf B.ringCatIsSheaf ((pullback i).obj L) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom L

local instance regularPowerPullbackTensorEquivalence :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj L).IsEquivalence :=
  @Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL

/-- The native integer-power comparison takes the actual pullback of an ordinary power
to the ordinary power of the actual pullback. -/
@[colib_tag "COL-1058",
  colib_ref "axiom_stacks_5ed82d14"
    "Algebra/Category/ModuleCat/Sheaf/TensorPowerMapSuccessor.lean:82-108"
    "ingredient" "The original native pullback-power successor comparison",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/PullbackTensorTrivialization.lean"
    "ingredient" "Actual pullback of the original tensor section"]
theorem pullbackIntegerTensorPowerIso_natTensorPowerRegularSection
    (U : X.Opens) (s : Γ(L, U)) (n : ℕ) :
    Hom.app (pullbackIntegerTensorPowerIso i L hL (n : ℤ)).hom (i ⁻¹ᵁ U)
      (pullbackSectionHom i (schemeTensorPower X L hL (n : ℤ)) U (i ⁻¹ᵁ U) le_rfl
        (natTensorPowerRegularSection X L U s n)) =
      natTensorPowerRegularSection B ((pullback i).obj L) (i ⁻¹ᵁ U)
        (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl s) n := by
  induction n with
  | zero =>
    change Hom.app
      (Stacks.TensorPowerPullback.pullbackUnitSheafIso i.toLRSHom.toShHom).hom (i ⁻¹ᵁ U)
      (pullbackSectionHom i (SheafOfModules.unit X.ringCatSheaf) U (i ⁻¹ᵁ U) le_rfl
        (1 : Γ(X, U))) = (1 : Γ(B, i ⁻¹ᵁ U))
    refine (congrArg
      (Hom.app (Stacks.TensorPowerPullback.pullbackUnitSheafIso i.toLRSHom.toShHom).hom
        (i ⁻¹ᵁ U))
      (pullbackSectionHom_preimage_self i (SheafOfModules.unit X.ringCatSheaf) U
        (1 : Γ(X, U)))).trans ?_
    exact Stacks.PullbackTensorCoherence.pullbackUnitComparison_oneSec i.toLRSHom.toShHom (op U)
  | succ n ih =>
    let P := schemeTensorPower X L hL (n : ℤ)
    let Q := (pullback i).obj L
    let SP := Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso
      X.presheaf X.ringCatIsSheaf L (n : ℤ)
    let SQ := Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso
      B.presheaf B.ringCatIsSheaf Q (n : ℤ)
    let T := Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i P L
    let E := tensorProductIso B.presheaf B.ringCatIsSheaf
      (pullbackIntegerTensorPowerIso i L hL (n : ℤ)) (Iso.refl Q)
    let t : Γ(tensorObj P L, U) :=
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        P L (natTensorPowerRegularSection X L U s n) s
    have hsquare : (pullback i).map SP.hom ≫
        (pullbackIntegerTensorPowerIso i L hL ((n : ℤ) + 1)).hom =
      T.hom ≫ E.hom ≫ SQ.hom :=
      Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_tensorPowerSuccIso
        X.presheaf X.ringCatIsSheaf B.presheaf B.ringCatIsSheaf (pullback i) L
        (Stacks.TensorPowerPullback.tensorFactorComparison i.toLRSHom.toShHom L)
        (Stacks.TensorPowerPullback.pullbackUnitSheafIso i.toLRSHom.toShHom) (n : ℤ)
    refine (congrArg
      (Hom.app (pullbackIntegerTensorPowerIso i L hL ((n : ℤ) + 1)).hom (i ⁻¹ᵁ U))
      (pullbackSectionHom_naturality_preimage i SP.hom U t).symm).trans ?_
    refine (congrArg (fun f => Hom.app f (i ⁻¹ᵁ U)
      (pullbackSectionHom i (tensorObj P L) U (i ⁻¹ᵁ U) le_rfl t)) hsquare).trans ?_
    refine (congrArg (fun z => Hom.app SQ.hom (i ⁻¹ᵁ U) (Hom.app E.hom (i ⁻¹ᵁ U) z))
      (Stacks.PullbackTensorIso.pullbackSectionHom_tensorSectionsAt i P L U
        (natTensorPowerRegularSection X L U s n) s)).trans ?_
    refine (congrArg (Hom.app SQ.hom (i ⁻¹ᵁ U))
      (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt B.presheaf B.ringCatIsSheaf
        (op (i ⁻¹ᵁ U)) _ _ _ _
        (pullbackIntegerTensorPowerIso i L hL (n : ℤ)) (Iso.refl Q) _ _)).trans ?_
    exact congrArg (fun z => Hom.app SQ.hom (i ⁻¹ᵁ U)
      (Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op (i ⁻¹ᵁ U))
        (schemeTensorPower B Q (inferInstance) (n : ℤ)) Q z
        (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl s))) ih

local instance regularPowerPullbackAGInvertible :
    SheafOfModules.IsInvertible B.presheaf (ringSheafCond B) ((pullback i).obj L) :=
  (regularPowerPullbackInvertible i L).toAlgebraicGeometry

local instance regularPowerPullbackMulCommutative :
    ∀ V, IsMulCommutative ((ringSheaf B).obj.obj V) :=
  fun V => inferInstanceAs (IsMulCommutative (B.presheaf.obj V))

/-- The specified root isomorphism transports the ordinary power to coordinate one in
the original target frame, using the original full-boundary compatibility equation. -/
@[colib_tag "COL-1058"]
theorem frame_rootImage_natTensorPowerRegularSection_preimage
    (P : X.Modules) (n : ℕ) (α : schemeTensorPower X L hL (n : ℤ) ≅ P)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (ringSheaf B))
    (τ : (pullback i).obj P ≅ SheafOfModules.unit (ringSheaf B))
    (hcompat : tensorPowerMap B e n ≪≫ structureSheafTensorPowerIso B n =
      (pullbackIntegerTensorPowerIso i L hL (n : ℤ)).symm ≪≫ (pullback i).mapIso α ≪≫ τ)
    (U : X.Opens) (m : Γ(L, U))
    (hm : Hom.app e.hom (i ⁻¹ᵁ U) (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl m) =
      (1 : Γ(B, i ⁻¹ᵁ U))) :
    Hom.app τ.hom (i ⁻¹ᵁ U)
      (pullbackSectionHom i P U (i ⁻¹ᵁ U) le_rfl
        (Hom.app α.hom U (natTensorPowerRegularSection X L U m n))) =
      (1 : Γ(B, i ⁻¹ᵁ U)) := by
  have hsquare : (pullbackIntegerTensorPowerIso i L hL (n : ℤ)).hom ≫
        (tensorPowerMap B e n ≪≫ structureSheafTensorPowerIso B n).hom =
      (pullback i).map α.hom ≫ τ.hom := by
    refine (congrArg (fun v =>
      (pullbackIntegerTensorPowerIso i L hL (n : ℤ)).hom ≫ v.hom) hcompat).trans ?_
    exact Iso.hom_inv_id_assoc (pullbackIntegerTensorPowerIso i L hL (n : ℤ))
      ((pullback i).map α.hom ≫ τ.hom)
  refine (congrArg (Hom.app τ.hom (i ⁻¹ᵁ U))
    (pullbackSectionHom_naturality_preimage i α.hom U
      (natTensorPowerRegularSection X L U m n)).symm).trans ?_
  refine (congrArg (fun f => Hom.app f (i ⁻¹ᵁ U)
    (pullbackSectionHom i (schemeTensorPower X L hL (n : ℤ)) U (i ⁻¹ᵁ U) le_rfl
      (natTensorPowerRegularSection X L U m n))) hsquare.symm).trans ?_
  refine (congrArg
    (Hom.app (tensorPowerMap B e n ≪≫ structureSheafTensorPowerIso B n).hom (i ⁻¹ᵁ U))
    (pullbackIntegerTensorPowerIso_natTensorPowerRegularSection i L U m n)).trans ?_
  exact tensorPowerFrame_natTensorPowerRegularSection_eq_one B ((pullback i).obj L)
    (i ⁻¹ᵁ U) (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl m) e hm n

/-- The target-frame normalization on the entire original boundary, with an actual
ordinary representative on an open containing that boundary. -/
@[colib_tag "COL-1058"]
theorem frame_rootImage_natTensorPowerRegularSection_boundary
    (P : X.Modules) (n : ℕ) (α : schemeTensorPower X L hL (n : ℤ) ≅ P)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (ringSheaf B))
    (τ : (pullback i).obj P ≅ SheafOfModules.unit (ringSheaf B))
    (hcompat : tensorPowerMap B e n ≪≫ structureSheafTensorPowerIso B n =
      (pullbackIntegerTensorPowerIso i L hL (n : ℤ)).symm ≪≫ (pullback i).mapIso α ≪≫ τ)
    (U : X.Opens) (hU : i ⁻¹ᵁ U = ⊤) (m : Γ(L, U))
    (hm : Hom.app e.hom ⊤ (pullbackSectionHom i L U ⊤ hU.ge m) = (1 : Γ(B, ⊤))) :
    Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hU.ge
      (Hom.app α.hom U (natTensorPowerRegularSection X L U m n))) = (1 : Γ(B, ⊤)) := by
  have hW : ∀ W : B.Opens, W = i ⁻¹ᵁ U → ∀ h : W ≤ i ⁻¹ᵁ U,
      Hom.app e.hom W (pullbackSectionHom i L U W h m) = (1 : Γ(B, W)) →
      Hom.app τ.hom W (pullbackSectionHom i P U W h
        (Hom.app α.hom U (natTensorPowerRegularSection X L U m n))) = (1 : Γ(B, W)) := by
    intro W hW h hm
    subst W
    exact frame_rootImage_natTensorPowerRegularSection_preimage i L P n α e τ hcompat U m hm
  exact hW ⊤ hU.symm hU.ge hm

end AlgebraicGeometry.Scheme.Modules
