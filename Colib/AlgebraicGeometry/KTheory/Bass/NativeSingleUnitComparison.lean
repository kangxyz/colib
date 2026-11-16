/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.NativeDoubleUnitQuotient
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeContractionBlockSwap
public import Colib.KTheory.Bass.TwoChartMapIso
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitComparison
public import Colib.AlgebraicGeometry.ProjectiveLine.PositiveBassChartComplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientConnectiveGroups
public import Colib.KTheory.Waldhausen.Iterated.ExactSelfTrackStableOperation
public import Colib.AlgebraicGeometry.Modules.PerfectGlobalUnit
public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackFunctor

/-! # Comparing the original Laurent unit operations on flat and perfect complexes -/

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

/-- The original forward Laurent operation in each connective degree. -/
def singleForwardUnit (n : ℕ) : quasiCompactKFunctor.{u} n ⟶ L ⋙ quasiCompactKFunctor (n + 1)
    where
  app X := AddCommGrpCat.ofHom (projectionUnitOperation ℓ X.unop.obj t n).toAdditive
  naturality {X Y} f := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (projectionUnitOperation_naturality ℓ f.unop.hom t n).symm

/-- The same original forward scalar followed by the genuine Laurent quotient. -/
def singleForwardQuotient (n : ℕ) :
    quasiCompactKFunctor.{u} n ⟶ contraction p m (quasiCompactKFunctor (n + 1)) :=
  singleForwardUnit n ≫ contractionπ p m (quasiCompactKFunctor (n + 1))

/-- Literal inclusion gives the comparison between the actual flat and perfect K-functors. -/
def singleUnitInclusionIso (n : ℕ) :
    quasiCompactKFunctor.{u} n ≅ connectivePerfectKFunctor n :=
  NatIso.ofComponents
    (fun X => (boundedAboveFlatPerfectKEquiv X.unop.obj.toRingedSpace n).toAdditive.toAddCommGrpIso)
    (fun {X Y} f => by
      apply AddCommGrpCat.ext
      intro x
      exact congrArg Additive.ofMul (DFunLike.congr_fun
        (boundedAboveFlatPerfectToPerfectKMap_pullback f.unop.hom n).symm x.toMul))

set_option maxHeartbeats 650000 in
-- Both original normalized scalar operations unfold the actual perfect inclusion.
/-- The actual flat scalar operation is carried by literal inclusion to the same perfect scalar. -/
theorem projectionUnitOperation_inclusion (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    let Y := laurentFunctor.obj X
    let f := (laurentProjection.app X).hom
    let q := relativeLaurentCoordinateUnit X
    (boundedAboveFlatPerfectToPerfectKMap Y.obj.toRingedSpace (n + 1)).comp
        (projectionUnitOperation ℓ X.obj t n) =
      (originalKSelfTrackOperation _ _ (perfectFlatUnitHomotopy f q) n).comp
        (boundedAboveFlatPerfectToPerfectKMap X.obj.toRingedSpace n) := by
  let Y := laurentFunctor.obj X
  let f := (laurentProjection.app X).hom
  let q := relativeLaurentCoordinateUnit X
  apply MonoidHom.ext
  intro x
  let A := boundedAboveFlatPerfectWaldhausen X.obj.toRingedSpace
  let B := boundedAboveFlatPerfectWaldhausen Y.obj.toRingedSpace
  let C := perfectComplexesWaldhausen X.obj.toRingedSpace
  let D := perfectComplexesWaldhausen Y.obj.toRingedSpace
  let H := boundedAboveFlatPerfectUnitHomotopy f q
  let J := perfectFlatUnitHomotopy f q
  let F := (stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
    (boundedAboveFlatPerfectToPerfectPrespectrumMap Y.obj.toRingedSpace)
  let G := (stableHomotopyFunctor (n : ℤ)).map
    (boundedAboveFlatPerfectToPerfectPrespectrumMap X.obj.toRingedSpace)
  let y := boundedAboveFlatPerfectToPerfectKMap X.obj.toRingedSpace n x
  let z := originalKStableEquiv A n (Additive.ofMul x)
  apply (originalKStableEquiv D (n + 1)).injective
  change originalKStableEquiv D (n + 1) (Additive.ofMul
    (boundedAboveFlatPerfectToPerfectKMap Y.obj.toRingedSpace (n + 1)
      (originalKSelfTrackOperation A B H n x))) =
    originalKStableEquiv D (n + 1)
      (Additive.ofMul (originalKSelfTrackOperation C D J n y))
  calc
    _ = F (originalKStableEquiv B (n + 1)
          (Additive.ofMul (originalKSelfTrackOperation A B H n x))) :=
      boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality _ _ _
    _ = F (H.stableOperation (n : ℤ) z) :=
      congrArg (fun a : stableHomotopyGroup (originalPrespectrum B) ((n + 1 : ℕ) : ℤ) ↦ F a)
        (originalKSelfTrackOperation_stable A B H n x)
    _ = J.stableOperation (n : ℤ) (G z) :=
      ConcreteCategory.congr_hom
        (boundedAboveFlatPerfectUnitHomotopy_stableOperation_inclusion f q (n : ℤ)) z
    _ = J.stableOperation (n : ℤ) (originalKStableEquiv C n (Additive.ofMul y)) :=
      congrArg (fun a : stableHomotopyGroup (originalPrespectrum C) (n : ℤ) ↦
        J.stableOperation (n : ℤ) a)
        (boundedAboveFlatPerfectToPerfectPrespectrumMap_originalK_naturality _ n x).symm
    _ = _ := (originalKSelfTrackOperation_stable C D J n y).symm

/-- The actual inverse perfect unit is the negative of the forward operation. -/
theorem perfectLaurentInverseOperation_eq_inv (X : QuasiCompactSchemes.{u}) (n : ℕ)
    (x : (perfectComplexesWaldhausen X.obj.toRingedSpace).K n) :
    positiveBassUnitSection X n x =
      (originalKSelfTrackOperation _ _
        (perfectFlatUnitHomotopy (laurentProjection.app X).hom
          (relativeLaurentCoordinateUnit X)) n x)⁻¹ := by
  let f := (laurentProjection.app X).hom
  let q := relativeLaurentCoordinateUnit X
  have hi : perfectFlatPullbackUnitIso f q⁻¹ = (perfectFlatPullbackUnitIso f q).symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    simp only [perfectFlatPullbackUnitIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      NatTrans.comp_app, Category.id_comp]
    exact congrArg Iso.hom (perfectGlobalUnitIso_app_inv _ q _)
  have hs : (perfectFlatUnitHomotopy f q⁻¹).stableOperation (n : ℤ) =
      -(perfectFlatUnitHomotopy f q).stableOperation (n : ℤ) := by
    unfold perfectFlatUnitHomotopy
    rw [hi]
    exact exactIsoSelfTrack_stableOperation_symm _ _ _ _ _
  let W := perfectComplexesWaldhausen (laurentFunctor.obj X).obj.toRingedSpace
  apply (originalKStableEquiv W (n + 1)).injective
  change originalKStableEquiv W (n + 1) (Additive.ofMul
    (originalKSelfTrackOperation _ _ (perfectFlatUnitHomotopy f q⁻¹) n x)) =
    originalKStableEquiv W (n + 1) (-(Additive.ofMul
      (originalKSelfTrackOperation _ _ (perfectFlatUnitHomotopy f q) n x)))
  rw [map_neg, originalKSelfTrackOperation_stable, originalKSelfTrackOperation_stable]
  exact ConcreteCategory.congr_hom hs _

/-- The perfect chart cokernel agrees with the geometric cokernel on actual representatives. -/
def perfectLaurentContractionIso (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    cokernel (positiveBassDifferenceHom X n) ≅
      (contraction p m (connectivePerfectKFunctor n)).obj (op X) := by
  let PP := (connectivePerfectKFunctor n).obj (op (polynomialFunctor.obj X))
  let e : AddCommGrpCat.of (Additive
      (((perfectComplexesWaldhausen (polynomialFunctor.obj X).obj.toRingedSpace).K n) ×
        ((perfectComplexesWaldhausen
          (polynomialFunctor.obj X).obj.toRingedSpace).K n))) ≅
      AddCommGrpCat.of (PP × PP) := (AddEquiv.refl _).toAddCommGrpIso
  let b := AddCommGrpCat.biprodIsoProd PP PP
  refine cokernel.mapIso _ _ (e ≪≫ b.symm) (Iso.refl _) ?_
  change positiveBassDifferenceHom X n ≫ 𝟙 _ =
    (e.hom ≫ b.inv) ≫ biprod.desc
      ((connectivePerfectKFunctor n).map (plus.app X).op)
      (-((connectivePerfectKFunctor n).map (minus.app X).op))
  rw [Category.comp_id, Category.assoc, AddCommGrpCat.biprodIsoProd_inv_comp_desc]
  rfl

end AlgebraicGeometry.Scheme.Modules.CoefficientDoubleNativeUnit
