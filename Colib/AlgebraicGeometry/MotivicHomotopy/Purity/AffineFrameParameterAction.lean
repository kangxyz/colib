/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineFrameAction
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.Support
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.UniversalFrameParameter

/-! # The universal frame action and its specializations on the original closed pairs -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k))) [IsAffine X.left]

set_option quotPrecheck false in
local notation "R" => Γ(X.left, ⊤)

section Matrix

variable (I : Type u) [Fintype I] [DecidableEq I]

local notation "B" => FrameParameterRing I R
local notation "Y" => frameParameterObject I X

/-- The generic invertible matrix as a matrix of global sections of the determinant open. -/
def frameParameterMatrixUnit : (Matrix I I Γ((Y).left, ⊤))ˣ :=
  Units.map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.mapMatrix.toMonoidHom)
    (isUnit_frameParameterMatrix I R).unit

set_option maxHeartbeats 500000 in
-- Compare matrices using the coefficient homomorphism across the affine spectrum.
theorem frameParameterMatrixUnit_val :
    (frameParameterMatrixUnit X I).val = (frameParameterMatrix I R).map
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom := by
  let f : B →+* Γ((Y).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let h := isUnit_frameParameterMatrix I R
  unfold frameParameterMatrixUnit
  exact congrArg (fun a : Matrix I I B => a.map f) h.unit_spec

end Matrix

variable (n : ℕ)

local notation "Y" => frameParameterObject (ULift (Fin n)) X

/-- The original affine-space automorphism acts on the pair with its marked origin. -/
def affineSpaceMatrixSupportArrowMap
    (A : (Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) R)ˣ) :
    Arrow.mk (closedPairOpenInclusion (relativeAffineSpaceZeroSection X n).left) ⟶
      Arrow.mk (closedPairOpenInclusion (relativeAffineSpaceZeroSection X n).left) :=
  closedSupportArrowMap (f := affineSpaceObjectMatrixMap X n A.val) (g := 𝟙 X)
    (affineSpaceOrigin_matrixMap_isPullback X n A)

/-- The universal frame matrix acts on the original pair of affine space and its origin. -/
def affineSpaceFrameParameterMap :
    Arrow.mk (closedPairOpenInclusion (relativeAffineSpaceZeroSection Y n).left) ⟶
      Arrow.mk (closedPairOpenInclusion (relativeAffineSpaceZeroSection Y n).left) :=
  affineSpaceMatrixSupportArrowMap Y n (frameParameterMatrixUnit X (ULift.{u} (Fin n)))

set_option maxHeartbeats 550000 in
-- The original affine-space maps have coefficient rings over different bases.
/-- On the closed pairs the universal action specializes to the given matrix action. -/
theorem affineSpaceFrameParameterMap_specialize
    (A : (Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) R)ˣ) :
    closedSupportArrowMap
        (affineSpaceOrigin_isPullback (frameParameterSmoothSection (ULift (Fin n)) X A) n) ≫
      affineSpaceFrameParameterMap X n =
      affineSpaceMatrixSupportArrowMap X n A ≫
        closedSupportArrowMap
          (affineSpaceOrigin_isPullback (frameParameterSmoothSection (ULift (Fin n)) X A) n) := by
  apply closedSupportArrowMap_eq_of_right
  let I := ULift.{u} (Fin n)
  let s : X ⟶ Y := frameParameterSmoothSection I X A
  change affineSpaceObjectMap s n ≫
      affineSpaceObjectMatrixMap Y n (frameParameterMatrixUnit X I).val =
      affineSpaceObjectMatrixMap X n A.val ≫ affineSpaceObjectMap s n
  rw [affineSpaceObjectMatrixMap_baseChange, frameParameterMatrixUnit_val,
    frameParameterSmoothSection_matrix]

/-- The section of the identity matrix gives the identity action on the original pair. -/
theorem affineSpaceFrameParameterMap_specialize_one :
    closedSupportArrowMap
        (affineSpaceOrigin_isPullback (frameParameterSmoothSection (ULift (Fin n)) X 1) n) ≫
      affineSpaceFrameParameterMap X n =
      closedSupportArrowMap
        (affineSpaceOrigin_isPullback (frameParameterSmoothSection (ULift (Fin n)) X 1) n) := by
  rw [affineSpaceFrameParameterMap_specialize]
  apply closedSupportArrowMap_eq_of_right
  let I := ULift.{u} (Fin n)
  have h : affineSpaceObjectMatrixMap X n (1 : Matrix I I R) = 𝟙 _ :=
    MorphismProperty.Over.Hom.ext AffineSpace.matrixMap_one
  change affineSpaceObjectMatrixMap X n (1 : Matrix I I R) ≫ _ = _
  rw [h, Category.id_comp]

end AlgebraicGeometry.MotivicHomotopy
