/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.LinearFrameChange

/-! # The matrix action on a marked smooth affine space -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable {S₀ : Scheme.{u}} (X : SmoothSite S₀) (n : ℕ)

/-- A frame matrix acts over the original base in the smooth site. -/
def affineSpaceObjectMatrixMap
    (A : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) Γ(X.left, ⊤)) :
    relativeAffineSpace X n ⟶ relativeAffineSpace X n :=
  homMk (AffineSpace.matrixMap A) (by
    let I := ULift.{u} (Fin n)
    change AffineSpace.matrixMap A ≫ ((AffineSpace I X.left ↘ X.left) ≫ X.hom) =
      (AffineSpace I X.left ↘ X.left) ≫ X.hom
    exact AffineSpace.matrixMap_over_assoc A X.hom)

@[reassoc (attr := simp)]
theorem affineSpaceOrigin_matrixMap
    (A : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) Γ(X.left, ⊤)) :
    relativeAffineSpaceZeroSection X n ≫ affineSpaceObjectMatrixMap X n A =
      relativeAffineSpaceZeroSection X n :=
  MorphismProperty.Over.Hom.ext (AffineSpace.origin_matrixMap A)

/-- Invertible frame changes preserve the actual closed pair. -/
theorem affineSpaceOrigin_matrixMap_isPullback
    (A : (Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) Γ(X.left, ⊤))ˣ) :
    IsPullback (relativeAffineSpaceZeroSection X n).left (𝟙 X.left)
      (affineSpaceObjectMatrixMap X n A.val).left (relativeAffineSpaceZeroSection X n).left :=
  let : IsIso (affineSpaceObjectMatrixMap X n A.val).left :=
    inferInstanceAs (IsIso (AffineSpace.matrixIso A).hom)
  IsPullback.of_vert_isIso ⟨by
    rw [Category.id_comp]
    exact congrArg (fun f => f.left) (affineSpaceOrigin_matrixMap X n A.val)⟩

/-- Specializing an original matrix of coefficients commutes with its action. -/
theorem affineSpaceObjectMatrixMap_baseChange {Y : SmoothSite S₀} (f : X ⟶ Y)
    (A : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) Γ(Y.left, ⊤)) :
    affineSpaceObjectMap f n ≫ affineSpaceObjectMatrixMap Y n A =
      affineSpaceObjectMatrixMap X n (A.map f.left.appTop.hom) ≫ affineSpaceObjectMap f n :=
  MorphismProperty.Over.Hom.ext (AffineSpace.matrixMap_baseChange f.left A)

end AlgebraicGeometry.MotivicHomotopy
