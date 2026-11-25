/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Path.SpanReassociation
public import Colib.Topology.Path.AssociatorEvaluation
public import Colib.Topology.Prespectrum.RelativeHomotopyOperationEvaluation
public import Colib.Topology.Prespectrum.RelativeHomotopyAssociatorEvaluation
public import Colib.Topology.Prespectrum.HomotopySquareComposition

/-! Scalar evaluation of the chosen five-piece span-map reassociation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Topology.LoopPrespectrum.NativeSpanReassociation
open Topology.LoopPrespectrum
variable {X : Type v} [TopologicalSpace X] {a b c d e f : X}
  {E F : LoopPrespectrum.{u}} {f0 f1 f2 f3 f4 f5 : E ⟶ F}
  (n : ℕ) (x : E.space n) (ev : X → F.space n)

private theorem trans {p q w : Path a b} {H K L : Homotopy f0 f1}
    (J : p.Homotopy q) (K' : q.Homotopy w)
    (J' : H.RelHomotopy K) (L' : K.RelHomotopy L)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hK : ∀ r s, ev (K' (r, s)) = L'.level n (r, (s, x))) (r s : I) :
    ev (J.trans K' (r, s)) = (J'.trans L').level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.trans_apply_path]
  exact Path.Evaluation.comparison_trans ev J K' (J'.path n x) (L'.path n x) hJ hK r s

private theorem hcomp {p q : Path a b} {w z : Path b c}
    {H H' : Homotopy f0 f1} {K K' : Homotopy f1 f2}
    (J : p.Homotopy q) (L : w.Homotopy z)
    (J' : H.RelHomotopy H') (L' : K.RelHomotopy K')
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hL : ∀ r s, ev (L (r, s)) = L'.level n (r, (s, x))) (r s : I) :
    ev (J.hcomp L (r, s)) = (J'.hcomp L').level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.hcomp_apply_path]
  exact Path.Evaluation.comparison_hcomp ev J L (J'.path n x) (L'.path n x) hJ hL r s

private theorem assoc (p : Path a b) (q : Path b c) (w : Path c d)
    (H : Homotopy f0 f1) (K : Homotopy f1 f2) (L : Homotopy f2 f3)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x))
    (hw : ∀ s, ev (w s) = L.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.transAssoc p q w (r, s)) =
      (Homotopy.RelHomotopy.transAssoc H K L).level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.transAssoc_apply_path]
  exact Path.Evaluation.transAssoc ev p q w (H.path n x) (K.path n x) (L.path n x)
    hp hq hw r s

private theorem path_trans (p : Path a b) (q : Path b c)
    (H : Homotopy f0 f1) (K : Homotopy f1 f2)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x)) (s : I) :
    ev ((p.trans q) s) = (H.trans K).level n (s, x) := by
  change ev ((p.trans q) s) = (H.trans K).path n x s
  rw [Homotopy.path_trans]
  exact Path.Evaluation.path_trans ev p q (H.path n x) (K.path n x) hp hq s

/-- Every one of the original three reassociation stages is retained at its original time. -/
theorem word (P : Path a b) (Q : Path b c) (T : Path c d) (U : Path d e) (V : Path e f)
    (P' : Homotopy f0 f1) (Q' : Homotopy f1 f2) (T' : Homotopy f2 f3)
    (U' : Homotopy f3 f4) (V' : Homotopy f4 f5)
    (hP : ∀ s, ev (P s) = P'.level n (s, x))
    (hQ : ∀ s, ev (Q s) = Q'.level n (s, x))
    (hT : ∀ s, ev (T s) = T'.level n (s, x))
    (hU : ∀ s, ev (U s) = U'.level n (s, x))
    (hV : ∀ s, ev (V s) = V'.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.spanReassociation P Q T U V (r, s)) =
      (((Homotopy.RelHomotopy.refl P').hcomp
        (Homotopy.RelHomotopy.transAssoc Q' (T'.trans U') V')).trans
        (((Homotopy.RelHomotopy.refl P').hcomp
          ((Homotopy.RelHomotopy.refl Q').hcomp
            (Homotopy.RelHomotopy.transAssoc T' U' V'))).trans
          (Homotopy.RelHomotopy.transAssoc P' Q' (T'.trans (U'.trans V'))).symm)).level n
            (r, (s, x)) := by
  have hp : ∀ r s : I, ev (Path.Homotopy.refl P (r, s)) =
      (Homotopy.RelHomotopy.refl P').level n (r, (s, x)) := fun _ s ↦ hP s
  have hq : ∀ r s : I, ev (Path.Homotopy.refl Q (r, s)) =
      (Homotopy.RelHomotopy.refl Q').level n (r, (s, x)) := fun _ s ↦ hQ s
  exact trans n x ev _ _ _ _
    (hcomp n x ev _ _ _ _ hp
      (assoc n x ev Q (T.trans U) V Q' (T'.trans U') V' hQ
        (path_trans n x ev T U T' U' hT hU) hV))
    (trans n x ev _ _ _ _
      (hcomp n x ev _ _ _ _ hp
        (hcomp n x ev _ _ _ _ hq (assoc n x ev T U V T' U' V' hT hU hV)))
      (fun r s ↦ assoc n x ev P Q (T.trans (U.trans V))
        P' Q' (T'.trans (U'.trans V')) hP hQ
        (path_trans n x ev T (U.trans V) T' (U'.trans V') hT
          (path_trans n x ev U V U' V' hU hV)) (unitInterval.symm r) s)) r s

end Topology.LoopPrespectrum.NativeSpanReassociation
