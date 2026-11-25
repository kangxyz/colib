/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Path.Homotopy.TwoSheetConjugation
public import Colib.Topology.Path.AssociatorEvaluation
public import Colib.Topology.Prespectrum.RelativeHomotopyAssociatorEvaluation
public import Colib.Topology.Prespectrum.RelativeHomotopyConjugationEvaluation

/-!
# Pointwise evaluation of the original conjugation between two distinct sheets

Adapted from Quillen's `RelativeHomotopyTwoSheetConjugationEvaluation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both relative and path times remain independent.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Topology.LoopPrespectrum.NativeTwoSheetConjugation
variable {X : Type v} [TopologicalSpace X] {a b c d : X}
  {E T : LoopPrespectrum.{u}} {f0 f1 f2 f3 : E ⟶ T}
  (n : ℕ) (x : E.space n) (ev : X → T.space n)

namespace Word
open Homotopy.RelHomotopy
/-- The original word with only its source transport given a reusable name. -/
def comparison {E T : LoopPrespectrum.{u}} {f g : E ⟶ T}
    (L : Homotopy f g) (U : Homotopy f f) (V : Homotopy g g)
    (N₀ : Homotopy f (zeroHom E T)) (N₁ : Homotopy g (zeroHom E T))
    (JU : (U.trans L).RelHomotopy (L.trans V))
    (JN : N₀.RelHomotopy (L.trans N₁)) :
    (U.conjugateToZero N₀).RelHomotopy (V.conjugateToZero N₁) := by
  let W := V.trans N₁
  have JU' : (U.trans (L.trans N₁)).RelHomotopy (L.trans W) :=
    (transAssoc U L N₁).symm.trans
      ((JU.hcomp (refl N₁)).trans (transAssoc L V N₁))
  have JC : (L.symm.trans (L.trans W)).RelHomotopy W :=
    (transAssoc L.symm L W).symm.trans
      (((reflSymmTrans L).symm.hcomp (refl W)).trans (reflTrans W))
  have J : ((L.trans N₁).symm.trans (U.trans (L.trans N₁))).RelHomotopy
      (N₁.symm.trans W) :=
    retypeSymmTransSource L N₁ (U.trans (L.trans N₁)) (N₁.symm.trans W)
      ((transAssoc N₁.symm L.symm (U.trans (L.trans N₁))).trans
        ((refl N₁.symm).hcomp (((refl L.symm).hcomp JU').trans JC)))
  exact (JN.symmPath.hcomp ((refl U).hcomp JN)).trans J

/-- Naming the source rewrite leaves the original native comparison itself unchanged. -/
theorem comparison_eq_original {E T : LoopPrespectrum.{u}} {f g : E ⟶ T}
    (L : Homotopy f g) (U : Homotopy f f) (V : Homotopy g g)
    (N₀ : Homotopy f (zeroHom E T)) (N₁ : Homotopy g (zeroHom E T))
    (JU : (U.trans L).RelHomotopy (L.trans V))
    (JN : N₀.RelHomotopy (L.trans N₁)) :
    comparison L U V N₀ N₁ JU JN = conjugateNaturality L U V N₀ N₁ JU JN := rfl
end Word

private theorem path_trans (p : Path a b) (q : Path b c)
    (H : Homotopy f0 f1) (K : Homotopy f1 f2)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x)) (s : I) :
    ev ((p.trans q) s) = (H.trans K).level n (s, x) := by
  change ev ((p.trans q) s) = (H.trans K).path n x s
  rw [Homotopy.path_trans]
  exact Path.Evaluation.path_trans ev p q (H.path n x) (K.path n x) hp hq s

private theorem path_symm (p : Path a b) (H : Homotopy f0 f1)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (s : I) :
    ev (p.symm s) = H.symm.level n (s, x) := hp _

private theorem comparison_refl (p : Path a b) (H : Homotopy f0 f1)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.refl p (r, s)) =
      (Homotopy.RelHomotopy.refl H).level n (r, (s, x)) := hp s

private theorem comparison_symm {p q : Path a b} {H K : Homotopy f0 f1}
    (J : p.Homotopy q) (J' : H.RelHomotopy K)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x))) (r s : I) :
    ev (J.symm (r, s)) = J'.symm.level n (r, (s, x)) := hJ _ s

private theorem comparison_trans {p q w : Path a b} {H K L : Homotopy f0 f1}
    (J : p.Homotopy q) (K' : q.Homotopy w)
    (J' : H.RelHomotopy K) (L' : K.RelHomotopy L)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hK : ∀ r s, ev (K' (r, s)) = L'.level n (r, (s, x))) (r s : I) :
    ev (J.trans K' (r, s)) = (J'.trans L').level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.trans_apply_path]
  exact Path.Evaluation.comparison_trans ev J K' (J'.path n x) (L'.path n x) hJ hK r s

private theorem comparison_hcomp {p q : Path a b} {w z : Path b c}
    {H H' : Homotopy f0 f1} {K K' : Homotopy f1 f2}
    (J : p.Homotopy q) (L : w.Homotopy z)
    (J' : H.RelHomotopy H') (L' : K.RelHomotopy K')
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x)))
    (hL : ∀ r s, ev (L (r, s)) = L'.level n (r, (s, x))) (r s : I) :
    ev (J.hcomp L (r, s)) = (J'.hcomp L').level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.hcomp_apply_path]
  exact Path.Evaluation.comparison_hcomp ev J L (J'.path n x) (L'.path n x) hJ hL r s

private theorem transAssoc (p : Path a b) (q : Path b c) (w : Path c d)
    (H : Homotopy f0 f1) (K : Homotopy f1 f2) (L : Homotopy f2 f3)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x))
    (hw : ∀ s, ev (w s) = L.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.transAssoc p q w (r, s)) =
      (Homotopy.RelHomotopy.transAssoc H K L).level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.transAssoc_apply_path]
  exact Path.Evaluation.transAssoc ev p q w (H.path n x) (K.path n x) (L.path n x)
    hp hq hw r s

private theorem reflTrans (p : Path a b) (H : Homotopy f0 f1)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.reflTrans p (r, s)) =
      (Homotopy.RelHomotopy.reflTrans H).level n (r, (s, x)) := by
  rw [Homotopy.RelHomotopy.reflTrans_apply_path]
  exact Path.Evaluation.reflTrans ev p (H.path n x) hp r s

private theorem comparison_symmPath {p q : Path a b} {H K : Homotopy f0 f1}
    (J : p.Homotopy q) (J' : H.RelHomotopy K)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x))) (r s : I) :
    ev (J.symm₂ (r, s)) = J'.symmPath.level n (r, (s, x)) := hJ r _

private theorem reflSymmTrans (p : Path a b) (H : Homotopy f0 f1)
    (hp : ∀ s, ev (p s) = H.level n (s, x)) (r s : I) :
    ev (Path.Homotopy.reflSymmTrans p (r, s)) =
      (Homotopy.RelHomotopy.reflSymmTrans H).level n (r, (s, x)) := by
  rw [Path.Homotopy.TwoSheetConjugation.reverseCancellation_apply,
    Homotopy.RelHomotopy.reflSymmTrans_apply_path]
  exact Path.Evaluation.reflTransSymm ev p.symm (H.path n x).symm
    (path_symm n x ev p H hp) r s

private theorem retypeSource (p : Path a b) (q : Path b c) (w : Path a d)
    (z : Path c d) (H : Homotopy f0 f1) (K : Homotopy f1 f2)
    (W : Homotopy f0 f3) (Z : Homotopy f2 f3)
    (J : ((q.symm.trans p.symm).trans w).Homotopy z)
    (J' : ((K.symm.trans H.symm).trans W).RelHomotopy Z)
    (hJ : ∀ r s, ev (J (r, s)) = J'.level n (r, (s, x))) (r s : I) :
    ev (Path.Homotopy.TwoSheetConjugation.retypeSource p q w z J (r, s)) =
      (Homotopy.RelHomotopy.retypeSymmTransSource H K W Z J').level n (r, (s, x)) := by
  rw [Path.Homotopy.TwoSheetConjugation.retypeSource_apply,
    Homotopy.RelHomotopy.retypeSymmTransSource_apply]
  exact hJ r s

/-- The two-sheet scalar word evaluates to the exact original native conjugation. -/
theorem comparison {a₀ a₁ b₀ b₁ c₀ c₁ : X} {f g : E ⟶ T}
    (U : Path a₀ a₁) (V : Path b₀ b₁) (L₀ : Path a₀ b₀) (L₁ : Path a₁ b₁)
    (N₀₀ : Path a₀ c₀) (N₀₁ : Path a₁ c₁) (N₁₀ : Path b₀ c₀) (N₁₁ : Path b₁ c₁)
    (L' : Homotopy f g) (U' : Homotopy f f) (V' : Homotopy g g)
    (N₀' : Homotopy f (zeroHom E T)) (N₁' : Homotopy g (zeroHom E T))
    (JU : (U.trans L₁).Homotopy (L₀.trans V))
    (JN₀ : N₀₀.Homotopy (L₀.trans N₁₀)) (JN₁ : N₀₁.Homotopy (L₁.trans N₁₁))
    (JU' : (U'.trans L').RelHomotopy (L'.trans V'))
    (JN' : N₀'.RelHomotopy (L'.trans N₁'))
    (hU : ∀ s, ev (U s) = U'.level n (s, x))
    (hV : ∀ s, ev (V s) = V'.level n (s, x))
    (hL₀ : ∀ s, ev (L₀ s) = L'.level n (s, x))
    (hL₁ : ∀ s, ev (L₁ s) = L'.level n (s, x))
    (hN₁₀ : ∀ s, ev (N₁₀ s) = N₁'.level n (s, x))
    (hN₁₁ : ∀ s, ev (N₁₁ s) = N₁'.level n (s, x))
    (hJU : ∀ r s, ev (JU (r, s)) = JU'.level n (r, (s, x)))
    (hJN₀ : ∀ r s, ev (JN₀ (r, s)) = JN'.level n (r, (s, x)))
    (hJN₁ : ∀ r s, ev (JN₁ (r, s)) = JN'.level n (r, (s, x))) (r s : I) :
    ev (Path.Homotopy.TwoSheetConjugation.comparison U V L₀ L₁ N₀₀ N₀₁ N₁₀ N₁₁ JU JN₀ JN₁ (r, s)) =
      (Homotopy.RelHomotopy.conjugateNaturality L' U' V' N₀' N₁' JU' JN').level
        n (r, (s, x)) := by
  rw [← Word.comparison_eq_original]
  have hW := path_trans n x ev V N₁₁ V' N₁' hV hN₁₁
  have hLN := path_trans n x ev L₁ N₁₁ L' N₁' hL₁ hN₁₁
  have hULN := path_trans n x ev U (L₁.trans N₁₁) U' (L'.trans N₁') hU hLN
  have hJUstep := comparison_trans n x ev _ _ _ _
    (comparison_symm n x ev _ _
      (transAssoc n x ev U L₁ N₁₁ U' L' N₁' hU hL₁ hN₁₁))
    (comparison_trans n x ev _ _ _ _
      (comparison_hcomp n x ev _ _ _ _ hJU (comparison_refl n x ev N₁₁ N₁' hN₁₁))
      (transAssoc n x ev L₀ V N₁₁ L' V' N₁' hL₀ hV hN₁₁))
  have hJC := comparison_trans n x ev _ _ _ _
    (comparison_symm n x ev _ _
      (transAssoc n x ev L₀.symm L₀ (V.trans N₁₁) L'.symm L' (V'.trans N₁')
        (path_symm n x ev L₀ L' hL₀) hL₀ hW))
    (comparison_trans n x ev _ _ _ _
      (comparison_hcomp n x ev _ _ _ _
        (comparison_symm n x ev _ _ (reflSymmTrans n x ev L₀ L' hL₀))
        (comparison_refl n x ev (V.trans N₁₁) (V'.trans N₁') hW))
      (reflTrans n x ev (V.trans N₁₁) (V'.trans N₁') hW))
  have hJ := retypeSource n x ev L₀ N₁₀ (U.trans (L₁.trans N₁₁))
    (N₁₀.symm.trans (V.trans N₁₁)) L' N₁' (U'.trans (L'.trans N₁'))
    (N₁'.symm.trans (V'.trans N₁')) _ _
    (comparison_trans n x ev _ _ _ _
      (transAssoc n x ev N₁₀.symm L₀.symm (U.trans (L₁.trans N₁₁))
        N₁'.symm L'.symm (U'.trans (L'.trans N₁'))
        (path_symm n x ev N₁₀ N₁' hN₁₀) (path_symm n x ev L₀ L' hL₀) hULN)
      (comparison_hcomp n x ev _ _ _ _
        (comparison_refl n x ev N₁₀.symm N₁'.symm (path_symm n x ev N₁₀ N₁' hN₁₀))
        (comparison_trans n x ev _ _ _ _
          (comparison_hcomp n x ev _ _ _ _
            (comparison_refl n x ev L₀.symm L'.symm (path_symm n x ev L₀ L' hL₀))
            hJUstep) hJC)))
  exact comparison_trans n x ev _ _ _ _
    (comparison_hcomp n x ev _ _ _ _ (comparison_symmPath n x ev _ _ hJN₀)
      (comparison_hcomp n x ev _ _ _ _ (comparison_refl n x ev U U' hU) hJN₁)) hJ r s

end Topology.LoopPrespectrum.NativeTwoSheetConjugation
