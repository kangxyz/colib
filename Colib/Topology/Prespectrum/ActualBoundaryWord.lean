/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-! The exact moving-square boundary word for a relative prespectrum homotopy. -/
/-! Source: `ActualBoundaryWord.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {a b c d : E ⟶ F}

/-- Generic statement of the exact word written in the native coefficient `boundary` definition. -/
def actualBoundaryWord {B : Homotopy a b} {K : Homotopy b c}
    {H : Homotopy a d} {A : Homotopy d c}
    (J : K.RelHomotopy ((B.symm.trans H).trans A)) :
    H.RelHomotopy ((B.trans K).trans A.symm) := by
  have route : (B.trans K).RelHomotopy (H.trans A) :=
    ((refl B).hcomp J).trans
      (((transAssoc B (B.symm.trans H) A).symm).trans
        ((((transAssoc B B.symm H).symm).hcomp (refl A)).trans
          ((((reflTransSymm B).symm.hcomp (refl H)).hcomp (refl A)).trans
            ((reflTrans H).hcomp (refl A)))))
  exact (transRefl H).symm.trans
    (((refl H).hcomp (reflTransSymm A)).trans
      (((transAssoc H A A.symm).symm).trans
        (route.symm.hcomp (refl A.symm))))
end Topology.LoopPrespectrum.Homotopy.RelHomotopy
