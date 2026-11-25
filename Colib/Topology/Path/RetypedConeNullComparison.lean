/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Path.CarrierConeBoundary
public import Colib.Topology.Path.Homotopy.ThreeRoutes

/-!
# Cone null comparisons with a retyped movement path

A whole movement-edge equation changes only the endpoint types. The comparison then
uses the original collapse, reassociations, and cancellation homotopies.

Adapted from `RetypedConeNullComparison.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Topology.CarrierPathSquare
variable {X : Type u} [TopologicalSpace X] {a b c a' b' : X}
  {E : Path a c} {G : Path b c} {L : Path a b}

/-- The old cone with only its source endpoint type replaced. -/
def Square.rebaseOld (_S : Square E G L (Path.refl c)) (Q : Path a' b')
    (h : ∀ s, Q s = L s) : Path a' c where
  toFun := E
  continuous_toFun := E.continuous
  source' := E.source.trans (L.source.symm.trans ((h 0).symm.trans Q.source))
  target' := E.target

/-- The new cone with only its source endpoint type replaced. -/
def Square.rebaseNew (_S : Square E G L (Path.refl c)) (Q : Path a' b')
    (h : ∀ s, Q s = L s) : Path b' c where
  toFun := G
  continuous_toFun := G.continuous
  source' := G.source.trans (L.target.symm.trans ((h 1).symm.trans Q.target))
  target' := G.target

/-- The square interior is unchanged; the whole lower rail proves its new type. -/
def Square.rebaseMovement (S : Square E G L (Path.refl c)) (Q : Path a' b')
    (h : ∀ s, Q s = L s) :
    Square (S.rebaseOld Q h) (S.rebaseNew Q h) Q (Path.refl c) where
  parameter := S.parameter
  at_zero := S.at_zero
  at_one := S.at_one
  left r := (S.left r).trans (h r).symm
  right := S.right

/-- Retyping preserves both independent coordinates of the complete cone comparison. -/
theorem Square.rebaseMovement_coneBoundary_apply
    (S : Square E G L (Path.refl c)) (Q : Path a' b') (h : ∀ s, Q s = L s)
    (r s : I) :
    (S.rebaseMovement Q h).coneBoundary (r, s) = S.coneBoundary (r, s) :=
  (S.rebaseMovement Q h).coneBoundary_natural S id (fun _ _ ↦ rfl) r s

end Topology.CarrierPathSquare

namespace Path.Homotopy
variable {X : Type u} [TopologicalSpace X] {a b c d e t : X}

/-- The literal five-stage original straight-positive comparison word. -/
def straightPositiveWord (A : Path a b) (B : Path b c) (Q : Path c d)
    (L : Path a e) (F : Path e d)
    (J : (B.trans Q).Homotopy (A.symm.trans (L.trans F))) :
    ((A.trans B).trans Q).Homotopy (L.trans F) :=
  (transAssoc A B Q).trans
    (((refl A).hcomp J).trans
      ((transAssoc A A.symm (L.trans F)).symm.trans
        (((reflTransSymm A).symm.hcomp (refl (L.trans F))).trans
          (reflTrans (L.trans F)))))

/-- The literal five-stage null comparison; neither clock nor terminal pause is flattened. -/
def pastedPositiveNullWord (A : Path a b) (B : Path b c) (Q : Path c d)
    (L : Path a e) (F : Path e d) (E : Path c t) (G : Path d t)
    (J : (B.trans Q).Homotopy (A.symm.trans (L.trans F)))
    (K : E.Homotopy (Q.trans G)) :
    (A.trans (B.trans E)).Homotopy (L.trans (F.trans G)) :=
  (transAssoc A B E).symm.trans
    (((refl (A.trans B)).hcomp K).trans
      ((transAssoc (A.trans B) Q G).symm.trans
        (((straightPositiveWord A B Q L F J).hcomp (refl G)).trans
          (transAssoc L F G))))

end Path.Homotopy
