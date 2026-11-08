/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Path.Homotopy.ThreeRoutes

/-!
# The signed return word of an actual square and projection

The supplied square, original return path and exact reversed terminal edges give a constructive
endpoint-fixed homotopy to the inverse composition track. All reassociations and cancellations
use the original path homotopies. No geometric filler is selected.
-/
/-! Implementation provenance: `Quillen/Topology/Path/SquareProjectionReturn.lean:22-60`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, coordinates,
endpoint casts, cancellations and path orientations are retained. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology
universe u v
namespace Path.Homotopy
variable {X : Type u} [TopologicalSpace X] {a b c d : X}
  {I : Path a b} {A₀ : Path a c} {A₁ : Path b d} {Z : Path c d}

/-- The exact return and reversed square edges give the inverse original composition path. -/
def squareProjectionReturn (J : (I.trans A₁).Homotopy (A₀.trans Z)) (P : Path b a) :
    ((P.symm.trans A₁).trans (Z.symm.trans A₀.symm)).Homotopy (I.trans P).symm := by
  have remove : ((I.symm.trans A₀).trans A₀.symm).Homotopy I.symm :=
    (transAssoc I.symm A₀ A₀.symm).trans
      (((refl I.symm).hcomp (reflTransSymm A₀).symm).trans (transRefl I.symm))
  have result : ((P.symm.trans A₁).trans (Z.symm.trans A₀.symm)).Homotopy
      (P.symm.trans I.symm) :=
    (transAssoc P.symm A₁ (Z.symm.trans A₀.symm)).trans
      (((refl P.symm).hcomp (transAssoc A₁ Z.symm A₀.symm).symm).trans
        ((refl P.symm).hcomp (((rotate J).symm.hcomp (refl A₀.symm)).trans remove)))
  exact result.cast rfl (Path.trans_symm I P).symm

variable {E : Type v} [TopologicalSpace E] (f : C(E, X))
  {a' b' c' d' : E} (A₀' : Path a' c') (A₁' : Path b' d') (P : Path b' a')
  {I' : Path (f a') (f b')} {Z' : Path (f c') (f d')}

/-- The fine return remains a single original mapped path before the two reversed edges. -/
def squareProjectionReturnMap
    (J : (I'.trans (A₁'.map f.continuous)).Homotopy
      ((A₀'.map f.continuous).trans Z')) :
    (((P.symm.trans A₁').map f.continuous).trans
      (Z'.symm.trans (A₀'.map f.continuous).symm)).Homotopy
        (I'.trans (P.map f.continuous)).symm := by
  simpa only [Path.map_trans, Path.map_symm] using
    squareProjectionReturn J (P.map f.continuous)

/-- A supplied comparison with the original composition track retains its exact reversal. -/
def squareProjectionReturnTrack
    (J : (I'.trans (A₁'.map f.continuous)).Homotopy
      ((A₀'.map f.continuous).trans Z'))
    {T : Path (f a') (f a')} (K : T.Homotopy (I'.trans (P.map f.continuous))) :
    (((P.symm.trans A₁').map f.continuous).trans
      (Z'.symm.trans (A₀'.map f.continuous).symm)).Homotopy T.symm :=
  (squareProjectionReturnMap f A₀' A₁' P J).trans K.symm₂.symm


end Path.Homotopy

attribute [colib_ref "quillen"
    "Quillen/Topology/Path/SquareProjectionReturn.lean:22-60"
    "adaptation"
    "The exact signed return word of a mapped square and projection"]
  Path.Homotopy.squareProjectionReturn
  Path.Homotopy.squareProjectionReturnMap
  Path.Homotopy.squareProjectionReturnTrack
