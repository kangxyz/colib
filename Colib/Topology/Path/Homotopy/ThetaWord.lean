/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! # Path cancellation for the original theta word

Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductNormalizedEndpoint.lean:29–63` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, coordinates and path concatenations are retained. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology

universe w

namespace Path.Homotopy

/-- Remove an actual final path using its original cancellation and associator witnesses. -/
def removeSuffix {X : Type w} [TopologicalSpace X] {a b c : X}
    (P : Path a b) (Q : Path b c) (R : Path a c) (J : (P.trans Q).Homotopy R) :
    P.Homotopy (R.trans Q.symm) :=
  (Path.Homotopy.transRefl P).symm.trans
    (((Path.Homotopy.refl P).hcomp (Path.Homotopy.reflTransSymm Q)).trans
      ((Path.Homotopy.transAssoc P Q Q.symm).symm.trans
        (J.hcomp (Path.Homotopy.refl Q.symm))))

/-- The exact Theta word retains the initial path while inserting the actual unit cancellation. -/
def thetaWord {X : Type w} [TopologicalSpace X] {a d0 d m0 m q r : X}
    (A : Path a d0) (T0 : Path d0 m0) (T1 : Path d m)
    (M : Path m m0) (E : Path m0 q) (S : Path m r) (B : Path r q)
    (Z : Path d0 d)
    (J : Z.symm.Homotopy (T1.trans (M.trans T0.symm)))
    (K : (M.trans E).Homotopy (S.trans B)) :
    (Z.symm.trans A.symm).Homotopy
      ((T1.trans S).trans (B.trans (A.trans (T0.trans E)).symm)) := by
  have J1 := (J.hcomp (Path.Homotopy.refl A.symm)).trans
    (Path.Homotopy.transAssoc T1 (M.trans T0.symm) A.symm)
  have J2 := (Path.Homotopy.refl T1).hcomp
    (Path.Homotopy.transAssoc M T0.symm A.symm)
  have J3 := (Path.Homotopy.refl T1).hcomp
    ((removeSuffix M E (S.trans B) K).hcomp
      (Path.Homotopy.refl (T0.symm.trans A.symm)))
  have J4 := (Path.Homotopy.refl T1).hcomp
    (Path.Homotopy.transAssoc (S.trans B) E.symm (T0.symm.trans A.symm))
  have J5 := (Path.Homotopy.refl T1).hcomp
    (Path.Homotopy.transAssoc S B (E.symm.trans (T0.symm.trans A.symm)))
  have J6 := (Path.Homotopy.transAssoc T1 S
    (B.trans (E.symm.trans (T0.symm.trans A.symm)))).symm
  have J7 := (Path.Homotopy.refl (T1.trans S)).hcomp
    ((Path.Homotopy.refl B).hcomp (Path.Homotopy.transAssoc E.symm T0.symm A.symm).symm)
  exact (J1.trans (J2.trans (J3.trans (J4.trans (J5.trans (J6.trans J7)))))).cast rfl
    (by rw [Path.trans_symm, Path.trans_symm])


end Path.Homotopy
