/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.NativeSingleUnitComparison

/-! # The original single Laurent unit quotient on bounded-flat perfect complexes -/

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

/-- The original inverse geometric section gives the negative of the actual native forward
quotient under the literal inclusion and cokernel comparisons. -/
theorem singleForwardQuotient_inclusion (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (-((singleForwardQuotient n).app (op X))) ≫
        (contractionMap p m (singleUnitInclusionIso (n + 1)).hom).app (op X) =
      (singleUnitInclusionIso n).hom.app (op X) ≫
        positiveBassInverseQuotientHom X n ≫ (perfectLaurentContractionIso X (n + 1)).hom := by
  have hπ : cokernel.π (positiveBassDifferenceHom X (n + 1)) ≫
      (perfectLaurentContractionIso X (n + 1)).hom =
      (contractionπ p m (connectivePerfectKFunctor (n + 1))).app (op X) := by
    change _ = cokernel.π (polynomialDifference p m (connectivePerfectKFunctor (n + 1)) (op X))
    simp only [perfectLaurentContractionIso, cokernel.mapIso_hom]
    rw [cokernel.π_desc, Iso.refl_hom, Category.id_comp]
    rfl
  have h : (-((singleForwardUnit n).app (op X))) ≫
      (singleUnitInclusionIso (n + 1)).hom.app ((L).obj (op X)) =
      (singleUnitInclusionIso n).hom.app (op X) ≫
        AddCommGrpCat.ofHom (positiveBassUnitSection X n).toAdditive := by
    apply AddCommGrpCat.ext
    intro x
    have hu := DFunLike.congr_fun (projectionUnitOperation_inclusion X n) x.toMul
    have hi := perfectLaurentInverseOperation_eq_inv X n
      (boundedAboveFlatPerfectToPerfectKMap X.obj.toRingedSpace n x.toMul)
    let F := boundedAboveFlatPerfectToPerfectKMap (laurentFunctor.obj X).obj.toRingedSpace (n + 1)
    let z := projectionUnitOperation ℓ X.obj t n x.toMul
    simp only [Preadditive.neg_comp, ConcreteCategory.comp_apply,
      AddCommGrpCat.hom_neg, AddMonoidHom.neg_apply]
    change -(Additive.ofMul (F z)) = Additive.ofMul (positiveBassUnitSection X n _)
    exact congrArg Additive.ofMul ((congrArg Inv.inv hu).trans hi.symm)
  let π := (contractionπ p m (connectivePerfectKFunctor (n + 1))).app (op X)
  let i := (singleUnitInclusionIso n).hom.app (op X)
  let a : (connectivePerfectKFunctor n).obj (op X) ⟶
      (L ⋙ connectivePerfectKFunctor (n + 1)).obj (op X) :=
    AddCommGrpCat.ofHom (positiveBassUnitSection X n).toAdditive
  let q : (L ⋙ connectivePerfectKFunctor (n + 1)).obj (op X) ⟶
      cokernel (positiveBassDifferenceHom X (n + 1)) :=
    cokernel.π (positiveBassDifferenceHom X (n + 1))
  let e := (perfectLaurentContractionIso X (n + 1)).hom
  calc
    _ = ((-((singleForwardUnit n).app (op X))) ≫
        (singleUnitInclusionIso (n + 1)).hom.app ((L).obj (op X))) ≫ π := by
      dsimp only [π]
      simp only [singleForwardQuotient, NatTrans.comp_app, ← Preadditive.neg_comp,
        Category.assoc, contractionMap_π]
    _ = (i ≫ a) ≫ π := congrArg (· ≫ π) h
    _ = i ≫ (a ≫ q) ≫ e := by
      calc
        (i ≫ a) ≫ π = (i ≫ a) ≫ q ≫ e := congrArg ((i ≫ a) ≫ ·) hπ.symm
        _ = _ := by simp only [Category.assoc]
    _ = _ := rfl

/-- Each actual forward unit quotient is invertible at every fixed qcqs scheme. -/
instance singleForwardQuotient_app_isIso (X : QuasiCompactSchemes.{u})
    [QuasiSeparatedSpace X.obj] (n : ℕ) :
    IsIso ((singleForwardQuotient n).app (op X)) := by
  let e := ((contractionFunctor p m).mapIso (singleUnitInclusionIso (n + 1))).app (op X)
  let h := (singleUnitInclusionIso n).app (op X) ≪≫
    asIso (positiveBassInverseQuotientHom X n) ≪≫ perfectLaurentContractionIso X (n + 1)
  have he : (-((singleForwardQuotient n).app (op X))) ≫ e.hom = h.hom :=
    singleForwardQuotient_inclusion X n
  let hcomp : IsIso ((-((singleForwardQuotient n).app (op X))) ≫ e.hom) :=
    he.symm ▸ inferInstanceAs (IsIso h.hom)
  let : IsIso (-((singleForwardQuotient n).app (op X))) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (-((singleForwardQuotient n).app (op X)))
      e.hom (inferInstanceAs (IsIso e.hom)) hcomp
  rw [← neg_neg ((singleForwardQuotient n).app (op X))]
  change IsIso (-(asIso (-((singleForwardQuotient n).app (op X))))).hom
  infer_instance

end AlgebraicGeometry.Scheme.Modules.CoefficientDoubleNativeUnit
