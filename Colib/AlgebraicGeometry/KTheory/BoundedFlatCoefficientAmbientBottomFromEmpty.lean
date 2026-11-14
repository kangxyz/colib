/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientEmptyOpenModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBottomChartExactness
public import Colib.AlgebraicGeometry.Scheme.GlobalAuxiliaryCoefficientPairs
public import Colib.KTheory.Bass.TwoChartStableMapInvertibility

/-!
# Bottom chart vanishing for the original ambient Bass stages

Support on the whole scheme is the actual supported theory of the empty open.
Its literal support-forgetful map is invertible at every finite-stage chart
vertex; therefore the proved supported bottom vanishing gives the ambient one.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Topology Topology.LoopPrespectrum KTheory.Bass KTheory.Bass.TwoChartStable
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (Q : Over (Spec R))

/-- The empty open with its original structural map to the coefficient base. -/
def ambientEmptyOpenObject : Over (Spec R) :=
  Over.mk ((⊥ : Q.left.Opens).ι ≫ Q.hom)

/-- The literal empty open immersion over the coefficient base. -/
def ambientEmptyOpenArrow : ambientEmptyOpenObject Q ⟶ Q :=
  Over.homMk (⊥ : Q.left.Opens).ι rfl

local instance : IsOpenImmersion (ambientEmptyOpenArrow Q).left := by
  change IsOpenImmersion (⊥ : Q.left.Opens).ι
  infer_instance

local instance : IsEmpty (ambientEmptyOpenObject Q).left := by
  change IsEmpty (↑(⊥ : Q.left.Opens) : Scheme)
  infer_instance

local instance : CompactSpace (ambientEmptyOpenObject Q).left := by infer_instance

private theorem emptyForgetModel_isIso (a : Under R) :
    IsIso (boundedAboveFlatCoefficientSupportedForgetModelMap (ambientEmptyOpenArrow Q) a) := by
  let : IsEmpty (space (op (ambientEmptyOpenObject Q), a)) :=
    Function.isEmpty (projection (op (ambientEmptyOpenObject Q), a))
  exact CoefficientEmptyOpen.supportedForget_isIso (schemeMap (ambientEmptyOpenArrow Q) a) _ rfl

private theorem emptyForget_isIso (i : ℕ) :
    IsIso (boundedAboveFlatCoefficientSupportedBassForget (ambientEmptyOpenArrow Q) i) := by
  let : ∀ a, IsIso ((boundedAboveFlatCoefficientSupportedForgetModelTransformation
      (ambientEmptyOpenArrow Q)).app a) := emptyForgetModel_isIso Q
  let : IsIso (boundedAboveFlatCoefficientSupportedForgetModelTransformation
      (ambientEmptyOpenArrow Q)) :=
    NatIso.isIso_of_isIso_app _
  unfold boundedAboveFlatCoefficientSupportedBassForget
  change IsIso ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (boundedAboveFlatCoefficientSupportedForgetModelTransformation
      (ambientEmptyOpenArrow Q)) CategoryTheory.Waldhausen.IteratedS.prespectrumFunctor))
  infer_instance

variable [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The actual ambient right Bass term vanishes at every finite-stage bottom degree. -/
theorem boundedAboveFlatCoefficientAmbientBottomBassRight_isZero (a : Under R) (i : ℕ) :
    IsZero (bassRightGroup
      (modelDiagramTwoChartSquare (boundedAboveFlatCoefficientSectionModelRow Q) i a)
      (-(i : ℤ))) := by
  let v := boundedAboveFlatCoefficientSupportedBassForget (ambientEmptyOpenArrow Q) i
  let : IsIso v := emptyForget_isIso Q i
  let h := ((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum)).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum).map v)).app (laurentUnderSquare R a)
  let : IsIso h := by dsimp only [h]; infer_instance
  let H := stableHomotopyFunctor (-(i : ℤ))
  let : IsIso (H.map h.left.left) := inferInstance
  let : IsIso (H.map h.left.right) := inferInstance
  let : IsIso (H.map h.right.left) := inferInstance
  let : IsIso (H.map h.right.right) := inferInstance
  let k := bassRightMap h (-(i : ℤ))
  let : IsIso k := by dsimp only [k]; infer_instance
  exact (boundedAboveFlatCoefficientSupportedBottomBassRight_isZero (ambientEmptyOpenArrow Q)
     a i).of_iso
    (asIso k).symm

end AlgebraicGeometry.Scheme.Modules
