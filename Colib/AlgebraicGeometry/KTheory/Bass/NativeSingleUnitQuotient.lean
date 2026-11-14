/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.NativeSingleUnitInvertibility
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # The original double Laurent unit quotient on bounded-flat perfect complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS
open Opposite Topology.LoopPrespectrum
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.Modules.ProductUnitInterchange
open KTheory.Bass.TwoChart

universe u

namespace AlgebraicGeometry.Scheme.Modules.CoefficientDoubleNativeUnit

attribute [local instance] Waldhausen.Additivity.KCommGroup

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local notation "p" => NatTrans.op plus
local notation "m" => NatTrans.op minus
local notation "L" => laurentFunctor.op
local notation "ℓ" => PolynomialLaurent.laurentProjection (CommRingCat.of (ULift ℤ))
local notation "t" => PolynomialLaurent.laurentCoordinate (CommRingCat.of (ULift ℤ))

/-- The two consecutive quotients use precisely the original ordered double Laurent arrow. -/
theorem doubleForwardQuotient_eq_single :
    doubleForwardQuotient =
      singleForwardQuotient 0 ≫ contractionMap p m (singleForwardQuotient 1) := by
  apply NatTrans.ext
  funext X
  simp only [singleForwardQuotient, NatTrans.comp_app, Category.assoc]
  rw [contractionMap_π]
  rfl

/-- The polynomial projection is a base change of a map of affine schemes. -/
theorem polynomialChart_quasiSeparated (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] : QuasiSeparatedSpace (polynomialFunctor.obj X).obj := by
  let q := PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ))
  let f := pullback.fst (specULiftZIsTerminal.from X.obj) q
  let : IsAffineHom q := inferInstance
  let : IsAffineHom f := MorphismProperty.pullback_fst _ _ inferInstance
  let : IsSeparated f := IsSeparated.of_isAffineHom f
  exact @quasiSeparatedSpace_of_quasiSeparated _ X.obj f inferInstance inferInstance

/-- The Laurent projection is a base change of a map of affine schemes. -/
theorem laurentChart_quasiSeparated (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] : QuasiSeparatedSpace (laurentFunctor.obj X).obj := by
  let f := pullback.fst (specULiftZIsTerminal.from X.obj) ℓ
  let : IsAffineHom ℓ := inferInstance
  let : IsAffineHom f := MorphismProperty.pullback_fst _ _ inferInstance
  let : IsSeparated f := IsSeparated.of_isAffineHom f
  exact @quasiSeparatedSpace_of_quasiSeparated _ X.obj f inferInstance inferInstance

set_option maxHeartbeats 600000 in
-- The actual native polynomial and Laurent inclusions reduce to the opposite chart objects.
/-- The actual double unit quotient is invertible at each quasi-compact quasi-separated scheme. -/
instance doubleForwardQuotient_app_isIso (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] : IsIso (doubleForwardQuotient.app (op X)) := by
  let α := singleForwardQuotient 1
  let : IsIso (α.app (polynomialFunctor.op.obj (op X))) := by
    change IsIso ((singleForwardQuotient 1).app (op (polynomialFunctor.obj X)))
    exact @singleForwardQuotient_app_isIso (polynomialFunctor.obj X)
      (polynomialChart_quasiSeparated X) 1
  let : IsIso (α.app (laurentFunctor.op.obj (op X))) := by
    change IsIso ((singleForwardQuotient 1).app (op (laurentFunctor.obj X)))
    exact @singleForwardQuotient_app_isIso (laurentFunctor.obj X)
      (laurentChart_quasiSeparated X) 1
  have hα : IsIso ((contractionMap p m α).app (op X)) :=
    isIso_contractionMap_app p m α (op X)
  have he : doubleForwardQuotient.app (op X) =
      (singleForwardQuotient 0).app (op X) ≫ (contractionMap p m α).app (op X) :=
    (NatTrans.congr_app doubleForwardQuotient_eq_single (op X)).trans
      (NatTrans.comp_app _ _ _)
  have h0 : IsIso ((singleForwardQuotient 0).app (op X)) :=
    singleForwardQuotient_app_isIso X 0
  have hc : IsIso ((singleForwardQuotient 0).app (op X) ≫
      (contractionMap p m α).app (op X)) := IsIso.comp_isIso' h0 hα
  exact Eq.mp (congrArg (fun f => IsIso f) he.symm) hc

/-- The actual swap is minus identity on the double quotient of the original degree-two group. -/
theorem doubleContractionSwap_KTwo_eq_neg_id (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] :
    doubleContractionSwap (quasiCompactKFunctor 2) (op X) = -𝟙 _ := by
  apply (cancel_epi (doubleForwardQuotient.app (op X))).mp
  rw [doubleForwardQuotient_swap, Preadditive.comp_neg, Category.comp_id]

/-- The four-variable block swap transfers the actual degree-two sign back to degree zero. -/
theorem doubleContractionSwap_KZero_eq_neg_id (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] :
    doubleContractionSwap (quasiCompactKFunctor 0) (op X) = -𝟙 _ := by
  let P := polynomialFunctor
  let L' := laurentFunctor
  let : QuasiSeparatedSpace (P.obj X).obj := polynomialChart_quasiSeparated X
  let : QuasiSeparatedSpace (L'.obj X).obj := laurentChart_quasiSeparated X
  let : QuasiSeparatedSpace (P.obj (P.obj X)).obj :=
    polynomialChart_quasiSeparated (P.obj X)
  let : QuasiSeparatedSpace (L'.obj (P.obj X)).obj :=
    laurentChart_quasiSeparated (P.obj X)
  let : QuasiSeparatedSpace (P.obj (L'.obj X)).obj :=
    polynomialChart_quasiSeparated (L'.obj X)
  let : QuasiSeparatedSpace (L'.obj (L'.obj X)).obj :=
    laurentChart_quasiSeparated (L'.obj X)
  have h₂ := doubleContractionSwap_neg_contraction_contraction_app
    (quasiCompactKFunctor 2) (op X) (doubleContractionSwap_KTwo_eq_neg_id (L'.obj (L'.obj X)))
  let : IsIso ((contractionMap p m (contractionMap p m doubleForwardQuotient)).app (op X)) :=
    @isIso_doubleContractionMap_app _ _ _ _ p m _ _ doubleForwardQuotient (op X)
      (doubleForwardQuotient_app_isIso (P.obj (P.obj X)))
      (doubleForwardQuotient_app_isIso (L'.obj (P.obj X)))
      (doubleForwardQuotient_app_isIso (P.obj (L'.obj X)))
      (doubleForwardQuotient_app_isIso (L'.obj (L'.obj X)))
  apply (cancel_mono
    ((contractionMap p m (contractionMap p m doubleForwardQuotient)).app (op X))).mp
  rw [← doubleContractionSwap_groupMap doubleForwardQuotient (op X), h₂]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id, Category.id_comp]

end AlgebraicGeometry.Scheme.Modules.CoefficientDoubleNativeUnit
