/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentializationColimitNaturality
public import Colib.Topology.Prespectrum.ZigzagSequentializationHomotopy

/-!
# Whole original families on the canonical ordinary zigzag colimit

The compatible whole families of actual recursive pushout maps descend through the actual
ordinary positive-stage colimit. Their original times, first solid arrow and telescope
bridge are unchanged. Together with the strict zero and composition laws, these formulas
carry a specified original composite nullhomotopy to the canonical ordinary construction.
-/
/-!
Implementation provenance: adapted from Quillen at
`ZigzagSequentializationColimitHomotopy.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)
    (E' V' : ℕ → LoopPrespectrum.{u})
    (a' : ∀ n, E' n ⟶ V' n) (b' : ∀ n, E' (n + 1) ⟶ V' n)
    (d₀ d₁ : ∀ n, E n ⟶ E' n) (v₀ v₁ : ∀ n, V n ⟶ V' n)
    (ha₀ : ∀ n, a n ≫ v₀ n = d₀ n ≫ a' n)
    (hb₀ : ∀ n, b n ≫ v₀ n = d₀ (n + 1) ≫ b' n)
    (ha₁ : ∀ n, a n ≫ v₁ n = d₁ n ≫ a' n)
    (hb₁ : ∀ n, b n ≫ v₁ n = d₁ (n + 1) ≫ b' n)
    (HE : ∀ n, Homotopy (d₀ n) (d₁ n)) (HV : ∀ n, Homotopy (v₀ n) (v₁ n))
    (hA : ∀ n k r x, (HV n).level k (r, (a n).map k x) =
      (a' n).map k ((HE n).level k (r, x)))
    (hB : ∀ n k r x, (HV n).level k (r, (b n).map k x) =
      (b' n).map k ((HE (n + 1)).level k (r, x)))

/-- The entire original recursive family descends through the actual ordinary colimit. -/
def ordinaryColimitHomotopy : Homotopy
    (ordinaryColimitMap E V a b E' V' a' b' d₀ v₀ ha₀ hb₀)
    (ordinaryColimitMap E V a b E' V' a' b' d₁ v₁ ha₁ hb₁) :=
  SequentialColimit.mapHomotopy _ _ _ _ _ _ _ _
    (fun n ↦ stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB (n + 1))
    (fun n ↦ stageHomotopy_transition E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB (n + 1))

/-- Every positive original stage retains the whole unchanged family time. -/
@[simp] theorem ordinaryColimitHomotopy_inclusion (n k : ℕ) (r : unitInterval)
    (x : (stage E V a b (n + 1)).space k) :
    (ordinaryColimitHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB).level k
        (r, (SequentialColimit.inclusion (positiveStage E V a b)
          (positiveTransition E V a b) n).map k x) =
      (SequentialColimit.inclusion (positiveStage E' V' a' b')
        (positiveTransition E' V' a' b') n).map k
          ((stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
            ha₀ hb₀ ha₁ hb₁ HE HV hA hB (n + 1)).level k (r, x)) :=
  by
    unfold ordinaryColimitHomotopy
    exact SequentialColimit.mapHomotopy_inclusion
      (positiveStage E V a b) (positiveTransition E V a b)
      (positiveStage E' V' a' b') (positiveTransition E' V' a' b') _ _ _ _ _ _ k n r x

/-- Each family-time slice is the ordinary map of those exact original vertex slices. -/
theorem ordinaryColimitHomotopy_at (r : unitInterval) :
    (ordinaryColimitHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB).at r =
      ordinaryColimitMap E V a b E' V' a' b' (fun i ↦ (HE i).at r)
        (fun i ↦ (HV i).at r)
        (fun i ↦ by apply Hom.ext; funext k; ext x; exact hA i k r x)
        (fun i ↦ by apply Hom.ext; funext k; ext x; exact hB i k r x) := by
  apply SequentialColimit.hom_ext
  intro i
  unfold ordinaryColimitMap
  rw [SequentialColimit.inclusion_map]
  apply Hom.ext
  funext k
  ext x
  exact (ordinaryColimitHomotopy_inclusion E V a b E' V' a' b' d₀ d₁ v₀ v₁
    ha₀ hb₀ ha₁ hb₁ HE HV hA hB i k r x).trans
      (congrArg (fun m ↦ (SequentialColimit.inclusion (positiveStage E' V' a' b')
        (positiveTransition E' V' a' b') i).map k (m.map k x))
          (stageHomotopy_at E V a b E' V' a' b' d₀ d₁ v₀ v₁
            ha₀ hb₀ ha₁ hb₁ HE HV hA hB r (i + 1)))

/-- The original first solid arrow is preserved at every whole-family time. -/
theorem ordinaryColimitHomotopy_initial (k : ℕ) (r : unitInterval) (x : (E 0).space k) :
    (ordinaryColimitHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB).level k (r, (initialColimitMap E V a b).map k x) =
      (initialColimitMap E' V' a' b').map k ((HE 0).level k (r, x)) := by
  change (ordinaryColimitHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
    ha₀ hb₀ ha₁ hb₁ HE HV hA hB).level k
      (r, (SequentialColimit.inclusion _ _ 0).map k ((a 0).map k x)) = _
  rw [ordinaryColimitHomotopy_inclusion]
  exact congrArg (fun y ↦ (SequentialColimit.inclusion (positiveStage E' V' a' b')
    (positiveTransition E' V' a' b') 0).map k y) (hA 0 k r x)

/-- The actual telescope bridge commutes with every original whole-family time. -/
theorem telescopeToOrdinaryColimit_homotopy (k : ℕ) (r : unitInterval)
    (q : (Telescope.prespectrum (stage E V a b) (transition E V a b)).space k) :
    (ordinaryColimitHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB).level k (r, (telescopeToOrdinaryColimit E V a b).map k q) =
        (telescopeToOrdinaryColimit E' V' a' b').map k
          ((inducedTelescopeHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
            ha₀ hb₀ ha₁ hb₁ HE HV hA hB).level k (r, q)) := by
  induction q using Quot.inductionOn with
  | h z =>
    obtain ⟨n, s, x⟩ := z
    change (ordinaryColimitHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB).level k
        (r, (SequentialColimit.inclusion (positiveStage E V a b)
          (positiveTransition E V a b) n).map k ((transition E V a b n).map k x)) =
        (SequentialColimit.inclusion (positiveStage E' V' a' b')
          (positiveTransition E' V' a' b') n).map k ((transition E' V' a' b' n).map k
            ((stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
              ha₀ hb₀ ha₁ hb₁ HE HV hA hB n).level k (r, x)))
    rw [ordinaryColimitHomotopy_inclusion]
    exact congrArg (fun y ↦ (SequentialColimit.inclusion (positiveStage E' V' a' b')
      (positiveTransition E' V' a' b') n).map k y)
        (stageHomotopy_transition E V a b E' V' a' b' d₀ d₁ v₀ v₁
          ha₀ hb₀ ha₁ hb₁ HE HV hA hB n k r x).symm

/-- Original whole input nullhomotopies descend to a literal ordinary-colimit nullhomotopy. -/
def ordinaryColimitNullhomotopy
    (NE : ∀ n, Homotopy (d₀ n) (zeroHom (E n) (E' n)))
    (NV : ∀ n, Homotopy (v₀ n) (zeroHom (V n) (V' n)))
    (hNA : ∀ n k r x, (NV n).level k (r, (a n).map k x) =
      (a' n).map k ((NE n).level k (r, x)))
    (hNB : ∀ n k r x, (NV n).level k (r, (b n).map k x) =
      (b' n).map k ((NE (n + 1)).level k (r, x))) :
    Homotopy (ordinaryColimitMap E V a b E' V' a' b' d₀ v₀ ha₀ hb₀)
      (zeroHom (ordinaryColimit E V a b) (ordinaryColimit E' V' a' b')) :=
  (ordinaryColimitHomotopy E V a b E' V' a' b' d₀
    (fun i ↦ zeroHom (E i) (E' i)) v₀ (fun i ↦ zeroHom (V i) (V' i)) ha₀ hb₀
    (fun i ↦ by apply Hom.ext; funext k; ext _x; exact (a' i).map_point k |>.symm)
    (fun i ↦ by apply Hom.ext; funext k; ext _x; exact (b' i).map_point k |>.symm)
    NE NV hNA hNB).cast rfl (ordinaryColimitMap_zero E V a b E' V' a' b')

end Topology.LoopPrespectrum.ZigzagSequentialization
