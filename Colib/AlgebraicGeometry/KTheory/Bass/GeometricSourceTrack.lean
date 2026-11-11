/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.WholeSeedWord
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricIndexSquare
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentCoefficient

/-! # The original whole scheme current-transition comparison

The actual original coefficient track, finite-stage seed and literal row target are retained.
No stable class substitutes for the whole map or normalized boundary homotopy.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricSeedCospan
open GeometricSquareInterchange WholeSeedCospan SquareConeStrength HomotopyWord
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (coefficient.app X)) (F.map (coefficient.app X)))
    (hH : ∀ {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
      (x : (F.obj X).space n),
      (F.map (laurent.op.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

/-- The original track with only its diagonal endpoint identity made explicit. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/GeometricSeedCospan.lean:49"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
def sourceTrack (X : Scheme.{u}ᵒᵖ) :
    Homotopy (((geometricSquare F).left.hom ≫ (geometricSquare F).hom.right).app X)
      (((geometricSquare F).left.hom ≫ (geometricSquare F).hom.right).app X) :=
  (H X).cast (congrArg (fun a => a.app X) (geometricSquare_diagonal F)).symm
    (congrArg (fun a => a.app X) (geometricSquare_diagonal F)).symm

include hH in
/-- The endpoint cast preserves the actual same-time naturality. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/GeometricSeedCospan.lean:57"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
theorem sourceTrack_naturality : Natural (sourceTrack F H) := hH

end KTheory.Bass.GeometricSeedCospan
