/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Path.CarrierSquareDescent
public import Colib.Topology.Prespectrum.ConeSquareMapMovingCoherence
public import Colib.Topology.Prespectrum.RelativeHomotopyOperationEvaluation

/-!
# Pointwise evaluation of the actual corrected boundary

Adapted from `Quillen/Topology/Prespectrum/CarrierCorrectedBoundaryEvaluation.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The existing square, collapse and
correction word are unchanged.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Topology.CarrierPathSquare

section PathPasting

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {a b c : X} {a' b' c' : Y}

private theorem eval_comparison_trans (f : X → Y) {p q w : Path a b} {p' q' w' : Path a' b'}
    (J : p.Homotopy q) (K : q.Homotopy w)
    (J' : p'.Homotopy q') (K' : q'.Homotopy w')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s))
    (hK : ∀ r s, f (K (r, s)) = K' (r, s)) (r s : I) :
    f (J.trans K (r, s)) = J'.trans K' (r, s) := by
  rw [Path.Homotopy.trans_apply, Path.Homotopy.trans_apply]
  split_ifs
  · exact hJ _ s
  · exact hK _ s

/-- Horizontal pasting changes path time only, leaving comparison time independent. -/
private theorem eval_comparison_hcomp (f : X → Y)
    {p q : Path a b} {w z : Path b c} {p' q' : Path a' b'} {w' z' : Path b' c'}
    (J : p.Homotopy q) (K : w.Homotopy z)
    (J' : p'.Homotopy q') (K' : w'.Homotopy z')
    (hJ : ∀ r s, f (J (r, s)) = J' (r, s))
    (hK : ∀ r s, f (K (r, s)) = K' (r, s)) (r s : I) :
    f (J.hcomp K (r, s)) = J'.hcomp K' (r, s) := by
  rw [Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
  split_ifs
  · exact hJ r _
  · exact hK r _

end PathPasting

open LoopPrespectrum
variable {X : Type v} [TopologicalSpace X] {a₀ b₀ a₁ b₁ : X}
  {p₀ : Path a₀ b₀} {p₁ p₂ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}
  {E F : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
  {H₀ : Homotopy f₀ g₀} {H₁ H₂ : Homotopy f₁ g₁}
  {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}

/-- The exact native collapse and correction word, before quotient descent. -/
def nativeCorrectedBoundary (S : H₀.Square H₁ L M) (R : H₁.RelHomotopy H₂) :
    H₀.RelHomotopy ((L.trans H₂).trans M.symm) :=
  S.toBoundary.trans
    (((Homotopy.RelHomotopy.refl L).hcomp R).hcomp
      (Homotopy.RelHomotopy.refl M.symm))

/-- Whole square and correction images suffice; the evaluator need not be continuous. -/
theorem correctedBoundary_native (Q : Square p₀ p₁ l m) (J : p₁.Homotopy p₂)
    (S : H₀.Square H₁ L M) (R : H₁.RelHomotopy H₂)
    (n : ℕ) (x : E.space n) (ev : X → F.space n)
    (hQ : ∀ r s, ev (Q.parameter (r, s)) = S.level n (r, (s, x)))
    (hJ : ∀ r s, ev (J (r, s)) = R.level n (r, (s, x))) (r s : I) :
    ev ((Q.toBoundary.trans
      (((Path.Homotopy.refl l).hcomp J).hcomp (Path.Homotopy.refl m.symm))) (r, s)) =
      (nativeCorrectedBoundary S R).level n (r, (s, x)) := by
  have hL (t : I) : ev (l t) = L.level n (t, x) :=
    (congrArg ev (Q.left t)).symm.trans ((hQ t 0).trans (S.left n t x))
  have hM (t : I) : ev (m t) = M.level n (t, x) :=
    (congrArg ev (Q.right t)).symm.trans ((hQ t 1).trans (S.right n t x))
  have hB (r s : I) : ev (Q.toBoundary (r, s)) =
      S.toBoundary.level n (r, (s, x)) :=
    (hQ (ThreeSideSquare.collapse (r, s)).1
      (ThreeSideSquare.collapse (r, s)).2).trans
        (S.toBoundary_apply n r s x).symm
  have hC (r s : I) : ev (((Path.Homotopy.refl l).hcomp J) (r, s)) =
      ((Homotopy.RelHomotopy.refl L).hcomp R).level n (r, (s, x)) := by
    rw [Homotopy.RelHomotopy.hcomp_apply_path]
    exact eval_comparison_hcomp ev _ _ _ _ (fun _ t ↦ hL t) hJ r s
  have hD (r s : I) : ev
      ((((Path.Homotopy.refl l).hcomp J).hcomp (Path.Homotopy.refl m.symm)) (r, s)) =
      (((Homotopy.RelHomotopy.refl L).hcomp R).hcomp
        (Homotopy.RelHomotopy.refl M.symm)).level n (r, (s, x)) := by
    rw [Homotopy.RelHomotopy.hcomp_apply_path]
    exact eval_comparison_hcomp ev _ _ _ _ hC
      (fun _ t ↦ hM (unitInterval.symm t)) r s
  let D := ((Homotopy.RelHomotopy.refl L).hcomp R).hcomp (Homotopy.RelHomotopy.refl M.symm)
  exact (eval_comparison_trans ev _ _ (S.toBoundary.path n x) (D.path n x)
    hB hD r s).trans (Homotopy.RelHomotopy.trans_apply_path S.toBoundary D n r s x).symm

end Topology.CarrierPathSquare

namespace Topology.LoopPrespectrum
variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))
  {e : E ⟶ E''} {l : F ⟶ F''} (T : Homotopy (f ≫ l) (e ≫ h))
  (A : Homotopy e (a ≫ c)) (B : Homotopy l (b ≫ d))
  (Q : T.Square (coneSquarePastedHomotopy f g h a b c d H K)
    (Homotopy.precomp f B) (A.postcomp h))

/-- The original corrected moving null square is precisely this full boundary descent. -/
theorem coneSquareCompositionMovingNullSquare_eq_boundary :
    coneSquareCompositionMovingNullSquare f g h a b c d H K T A B Q =
      (Topology.CarrierPathSquare.nativeCorrectedBoundary
        (coneSquareNullMovingSquare f h T
          (coneSquarePastedHomotopy f g h a b c d H K) A B Q)
        (coneSquareCompositionNullComparison f g h a b c d H K)).toSquare := rfl

end Topology.LoopPrespectrum
