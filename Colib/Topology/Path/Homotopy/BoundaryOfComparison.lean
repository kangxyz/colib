/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Path.Homotopy.ThreeRoutes

/-! Literal scalar word of the native coefficient moving-square boundary. -/
/-! Source: `BoundaryOfComparison.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.Homotopy
variable {X : Type u} [TopologicalSpace X] {a b c d : X}

/-- The same rotations, cancellations, and pauses as native coefficient `boundary`. -/
def boundaryOfComparison {B : Path a b} {K : Path b c}
    {H : Path a d} {A : Path d c}
    (J : K.Homotopy ((B.symm.trans H).trans A)) :
    H.Homotopy ((B.trans K).trans A.symm) := by
  have route : (B.trans K).Homotopy (H.trans A) :=
    ((refl B).hcomp J).trans
      (((transAssoc B (B.symm.trans H) A).symm).trans
        ((((transAssoc B B.symm H).symm).hcomp (refl A)).trans
          ((((reflTransSymm B).symm.hcomp (refl H)).hcomp (refl A)).trans
            ((reflTrans H).hcomp (refl A)))))
  exact (transRefl H).symm.trans
    (((refl H).hcomp (reflTransSymm A)).trans
      (((transAssoc H A A.symm).symm).trans
        (route.symm.hcomp (refl A.symm))))
end Path.Homotopy
