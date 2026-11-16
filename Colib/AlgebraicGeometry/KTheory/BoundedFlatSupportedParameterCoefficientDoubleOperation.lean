/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedParameterCoefficientUnitOperation

/-!
# The two unchanged supported parameter tracks at the original coefficient quotients

Both actual Laurent Spec maps are retained while transporting the two original
stable operations and their successive coefficient cokernel projections.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
SupportedParameterCoefficientDoubleOperation.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedParameterCoefficientUnitOperation
open GlobalSupportedSection GlobalSectionChangeIndex GlobalSupportedParameterCoefficient
attribute [local irreducible] ParameterModels.supported
  boundedAboveFlatCoefficientSupportedModelFunctor ParameterLaurentTrack.supportedTrack
  boundedAboveFlatCoefficientSupportedLaurentAction
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

private def parameterLaurentMap (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    laurent.op.obj (specUnder.obj a) ⟶ specUnder.obj ((laurentUnderFunctor _).obj a) :=
  (laurentSpecIso a.right).hom.op

private theorem quotient_square {C : Type*} [Category C] {A B D E F : C}
    (p : A ⟶ B) (q : B ⟶ D) (i : A ⟶ E) (j : E ⟶ D) (π : D ⟶ F)
    (h : p ≫ q = i ≫ j) : i ≫ (j ≫ π) = p ≫ q ≫ π := by
  rw [← Category.assoc, ← h, Category.assoc]

private theorem laurent_stable_factor (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (prespectrumFunctor ⋙ stableHomotopyFunctor d).map (coefficientLaurentModelMap f a) =
      (prespectrumFunctor ⋙ stableHomotopyFunctor d).map
          ((ParameterModels.supported f.left).map (parameterLaurentMap a)) ≫
        (prespectrumFunctor ⋙ stableHomotopyFunctor d).map
          (coefficientModelMap f ((laurentUnderFunctor _).obj a)) :=
  (congrArg (prespectrumFunctor ⋙ stableHomotopyFunctor d).map
    (coefficientLaurentModelMap_factor f a)).trans
      ((prespectrumFunctor ⋙ stableHomotopyFunctor d).map_comp _ _)

private theorem left_factor {C : Type*} [Category C] {A B D E : C}
    (p : A ⟶ B) (q : B ⟶ D) (r : B ⟶ E) (s : E ⟶ D) (i : A ⟶ D)
    (hq : q = r ≫ s) (hp : p ≫ q = i) : p ≫ r ≫ s = i := by
  rw [← hq]
  exact hp

set_option backward.isDefEq.respectTransparency.types false in
private theorem firstOperation_factor (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((ParameterLaurentTrack.supportedTrack f.left).homotopy (specUnder.obj a)).stableOperation 0 ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        ((ParameterModels.supported f.left).map (parameterLaurentMap a)) ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        (coefficientModelMap f ((laurentUnderFunctor _).obj a)) =
    (prespectrumFunctor ⋙ stableHomotopyFunctor 0).map (coefficientModelMap f a) ≫
      ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy a).stableOperation 0 :=
  left_factor _ _ _ _ _ (laurent_stable_factor f a 1) (coefficientOperation f a 0)

private theorem doubleLaurent_stable_factor (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map (doubleLaurentModelMap f a) =
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        ((ParameterModels.supported f.left).map
          (laurent.op.map (parameterLaurentMap a))) ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        (coefficientLaurentModelMap f ((laurentUnderFunctor _).obj a)) :=
  (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map_comp _ _

set_option backward.isDefEq.respectTransparency.types false in
private theorem parameterLaurentOperation_square (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((ParameterLaurentTrack.supportedTrack f.left).homotopy
      (laurent.op.obj (specUnder.obj a))).stableOperation 1 ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        ((ParameterModels.supported f.left).map
          (laurent.op.map (parameterLaurentMap a))) =
    (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        ((ParameterModels.supported f.left).map (parameterLaurentMap a)) ≫
      ((ParameterLaurentTrack.supportedTrack f.left).homotopy
        (specUnder.obj ((laurentUnderFunctor _).obj a))).stableOperation 1 :=
  (parameterOperation_naturality f.left
    (X := laurent.op.obj (specUnder.obj a))
    (Y := specUnder.obj ((laurentUnderFunctor _).obj a)) (parameterLaurentMap a) 1).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem secondCoefficientOperation (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((ParameterLaurentTrack.supportedTrack f.left).homotopy
        (specUnder.obj ((laurentUnderFunctor _).obj a))).stableOperation 1 ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        (coefficientLaurentModelMap f ((laurentUnderFunctor _).obj a)) =
    (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        (coefficientModelMap f ((laurentUnderFunctor _).obj a)) ≫
      ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy
        ((laurentUnderFunctor _).obj a)).stableOperation 1 :=
  coefficientOperation f ((laurentUnderFunctor _).obj a) 1

private theorem postassoc {C : Type*} [Category C] {A B D E F : C}
    (p : A ⟶ B) (q : B ⟶ D) (r : A ⟶ E) (s : E ⟶ D) (t : D ⟶ F)
    (h : p ≫ q = r ≫ s) : p ≫ q ≫ t = r ≫ s ≫ t := by
  rw [← Category.assoc, h, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
private theorem parameterLaurentOperation_postcomp
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((ParameterLaurentTrack.supportedTrack f.left).homotopy
      (laurent.op.obj (specUnder.obj a))).stableOperation 1 ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        ((ParameterModels.supported f.left).map (laurent.op.map (parameterLaurentMap a))) ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        (coefficientLaurentModelMap f ((laurentUnderFunctor _).obj a)) =
    (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        ((ParameterModels.supported f.left).map (parameterLaurentMap a)) ≫
      ((ParameterLaurentTrack.supportedTrack f.left).homotopy
        (specUnder.obj ((laurentUnderFunctor _).obj a))).stableOperation 1 ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        (coefficientLaurentModelMap f ((laurentUnderFunctor _).obj a)) := by
  refine postassoc _ _ _ _ _ ?_
  exact parameterLaurentOperation_square f a

private theorem preassoc {C : Type*} [Category C] {A B D E F : C}
    (p : A ⟶ B) (q : B ⟶ D) (r : D ⟶ E) (s : B ⟶ F) (t : F ⟶ E)
    (h : q ≫ r = s ≫ t) : p ≫ q ≫ r = p ≫ s ≫ t := by
  rw [h]

set_option backward.isDefEq.respectTransparency.types false in
private theorem secondCoefficientOperation_precomp
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        ((ParameterModels.supported f.left).map (parameterLaurentMap a)) ≫
      ((ParameterLaurentTrack.supportedTrack f.left).homotopy
        (specUnder.obj ((laurentUnderFunctor _).obj a))).stableOperation 1 ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        (coefficientLaurentModelMap f ((laurentUnderFunctor _).obj a)) =
    (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        ((ParameterModels.supported f.left).map (parameterLaurentMap a)) ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        (coefficientModelMap f ((laurentUnderFunctor _).obj a)) ≫
      ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy
        ((laurentUnderFunctor _).obj a)).stableOperation 1 := by
  refine preassoc _ _ _ _ _ ?_
  exact secondCoefficientOperation f a

set_option backward.isDefEq.respectTransparency.types false in
private theorem secondOperation_factor (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((ParameterLaurentTrack.supportedTrack f.left).homotopy
      (laurent.op.obj (specUnder.obj a))).stableOperation 1 ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        ((ParameterModels.supported f.left).map (laurent.op.map (parameterLaurentMap a))) ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map
        (coefficientLaurentModelMap f ((laurentUnderFunctor _).obj a)) =
    (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        ((ParameterModels.supported f.left).map (parameterLaurentMap a)) ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        (coefficientModelMap f ((laurentUnderFunctor _).obj a)) ≫
      ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy
        ((laurentUnderFunctor _).obj a)).stableOperation 1 :=
  (parameterLaurentOperation_postcomp f a).trans (secondCoefficientOperation_precomp f a)

set_option backward.isDefEq.respectTransparency.types false in
private theorem secondOperation_unfactor (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((ParameterLaurentTrack.supportedTrack f.left).homotopy
      (laurent.op.obj (specUnder.obj a))).stableOperation 1 ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 2).map (doubleLaurentModelMap f a) =
    (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        ((ParameterModels.supported f.left).map (parameterLaurentMap a)) ≫
      (prespectrumFunctor ⋙ stableHomotopyFunctor 1).map
        (coefficientModelMap f ((laurentUnderFunctor _).obj a)) ≫
      ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy
        ((laurentUnderFunctor _).obj a)).stableOperation 1 := by
  rw [doubleLaurent_stable_factor]
  exact secondOperation_factor f a

private theorem paste_first {C : Type*} [Category C] {A B D E F G H : C}
    (p : A ⟶ B) (q : B ⟶ D) (k : D ⟶ E) (g : B ⟶ F)
    (h : F ⟶ G) (s : G ⟶ E) (i : A ⟶ H) (t : H ⟶ G)
    (hp : p ≫ g ≫ h = i ≫ t) (hq : q ≫ k = g ≫ h ≫ s) :
    (p ≫ q) ≫ k = i ≫ (t ≫ s) := by
  calc
    _ = p ≫ (q ≫ k) := Category.assoc _ _ _
    _ = p ≫ (g ≫ h ≫ s) := congrArg (fun v => p ≫ v) hq
    _ = (p ≫ g ≫ h) ≫ s := by simp only [Category.assoc]
    _ = (i ≫ t) ≫ s := congrArg (fun v => v ≫ s) hp
    _ = _ := Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The two unchanged parameter operations represent the two actual supported coefficient
operations through the complete specified twice-Laurent comparison. -/
theorem doubleOperation (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    SupportedParameterDoubleUnit.doubleUnit f.left (specUnder.obj a) ≫
        (stableHomotopyFunctor 2).map (prespectrumMap (doubleLaurentModelMap f a)) =
      (stableHomotopyFunctor 0).map (prespectrumMap (coefficientModelMap f a)) ≫
        boundedAboveFlatCoefficientSupportedDoubleForwardUnitMap f a 0 := by
  unfold SupportedParameterDoubleUnit.doubleUnit
    boundedAboveFlatCoefficientSupportedDoubleForwardUnitMap
  exact paste_first _ _ _ _ _ _ _ _ (firstOperation_factor f a) (secondOperation_unfactor f a)

/-- The original α₀ followed by contracted α₁ keeps both unchanged parameter operations and
the two original coefficient quotient projections. -/
theorem doubleForwardQuotient_parameter (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (stableHomotopyFunctor 0).map (prespectrumMap (coefficientModelMap f a)) ≫
        (boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient f 0).app a =
      SupportedParameterDoubleUnit.doubleUnit f.left (specUnder.obj a) ≫
        (stableHomotopyFunctor 2).map (prespectrumMap (doubleLaurentModelMap f a)) ≫
        KTheory.Bass.TwoChart.doubleContractionπ (underToLaurent _) (underToLaurentInvert _)
          (boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⋙
            stableHomotopyFunctor 2) a := by
  rw [boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient_representative]
  exact quotient_square _ _ _ _ _ (doubleOperation f a)

end AlgebraicGeometry.Scheme.Modules.SupportedParameterCoefficientUnitOperation
