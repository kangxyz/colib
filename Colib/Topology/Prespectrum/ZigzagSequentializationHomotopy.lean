/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentializationNaturality
public import Colib.Topology.Prespectrum.PushoutMapHomotopy
public import Colib.Topology.Prespectrum.TelescopeHomotopy

/-!
# Whole original families on canonical zigzag sequentialization

Strictly compatible whole homotopies on both original vertex families induce whole
homotopies on the unchanged recursive pushouts and their telescope. The original family
time, pushout cylinder height and prespectrum structure time remain independent.
-/
/-!
Implementation provenance: adapted from Quillen at
`ZigzagSequentializationHomotopy.lean` in its original source owner.
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

/-- Each positive recursive family retains its entire original comparison square. -/
def stageHomotopyWithComparison : (n : ℕ) →
    {L : Homotopy
      (stageMap E V a b E' V' a' b' d₀ v₀ ha₀ hb₀ (n + 1))
      (stageMap E V a b E' V' a' b' d₁ v₁ ha₁ hb₁ (n + 1)) //
      ∀ k r x, L.level k (r, (comparison E V a b (n + 1)).map k x) =
        (comparison E' V' a' b' (n + 1)).map k ((HE (n + 1)).level k (r, x))}
  | 0 => ⟨HV 0, hB 0⟩
  | n + 1 =>
    let previous := stageHomotopyWithComparison n
    ⟨HomotopyPushout.mapHomotopy
      (comparison E V a b (n + 1)) (a (n + 1))
      (comparison E' V' a' b' (n + 1)) (a' (n + 1))
      (comparison_naturality E V a b E' V' a' b' d₀ v₀ ha₀ hb₀ (n + 1)) (ha₀ (n + 1))
      (comparison_naturality E V a b E' V' a' b' d₁ v₁ ha₁ hb₁ (n + 1)) (ha₁ (n + 1))
      (HE (n + 1)) previous.1 (HV (n + 1)) previous.2 (hA (n + 1)), by
        intro k r x
        exact congrArg (HomotopyPushout.right
          (comparison E' V' a' b' (n + 1)) (a' (n + 1)) k) (hB (n + 1) k r x)⟩

/-- The original whole input homotopies induce the whole family on every actual stage. -/
def stageHomotopy : (n : ℕ) → Homotopy
    (stageMap E V a b E' V' a' b' d₀ v₀ ha₀ hb₀ n)
    (stageMap E V a b E' V' a' b' d₁ v₁ ha₁ hb₁ n)
  | 0 => HE 0
  | n + 1 => (stageHomotopyWithComparison E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB n).1

/-- Comparison arrows commute for every value of the unchanged original family time. -/
theorem stageHomotopy_comparison (n k : ℕ) (r : unitInterval) (x : (E n).space k) :
    (stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB n).level k
        (r, (comparison E V a b n).map k x) =
      (comparison E' V' a' b' n).map k ((HE n).level k (r, x)) := by
  cases n with
  | zero => rfl
  | succ n => exact (stageHomotopyWithComparison E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB n).2 k r x

/-- Transition arrows commute for every value of the unchanged original family time. -/
theorem stageHomotopy_transition (n k : ℕ) (r : unitInterval)
    (x : (stage E V a b n).space k) :
    (transition E' V' a' b' n).map k
        ((stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB n).level k
          (r, x)) =
      (stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB (n + 1)).level k
        (r, (transition E V a b n).map k x) := by
  cases n with
  | zero => exact (hA 0 k r x).symm
  | succ n => rfl

/-- Every family-time slice is the recursive map of those exact original input slices. -/
theorem stageHomotopy_at (r : unitInterval) (n : ℕ) :
    (stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB n).at r =
      stageMap E V a b E' V' a' b' (fun i ↦ (HE i).at r) (fun i ↦ (HV i).at r)
        (fun i ↦ by apply Hom.ext; funext k; ext x; exact hA i k r x)
        (fun i ↦ by apply Hom.ext; funext k; ext x; exact hB i k r x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      apply Hom.ext
      funext k
      ext z
      induction z using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z with
          | inl x =>
            exact congrArg (HomotopyPushout.left
              (comparison E' V' a' b' (n + 1)) (a' (n + 1)) k)
                (congrArg (fun m ↦ m.map k x) ih)
          | inr x => rfl
        | inr z => rfl

/-- The complete recursive family descends through the actual strict telescope construction. -/
def inducedTelescopeHomotopy : Homotopy
    (inducedTelescopeMap E V a b E' V' a' b' d₀ v₀ ha₀ hb₀)
    (inducedTelescopeMap E V a b E' V' a' b' d₁ v₁ ha₁ hb₁) :=
  Telescope.mapHomotopy _ _ _ _ _ _ _ _
    (stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB)
    (stageHomotopy_transition E V a b E' V' a' b' d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB)

/-- Every whole telescope-family slice is the map of the original input slices. -/
theorem inducedTelescopeHomotopy_at (r : unitInterval) :
    (inducedTelescopeHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB).at r =
      inducedTelescopeMap E V a b E' V' a' b' (fun i ↦ (HE i).at r)
        (fun i ↦ (HV i).at r)
        (fun i ↦ by apply Hom.ext; funext k; ext x; exact hA i k r x)
        (fun i ↦ by apply Hom.ext; funext k; ext x; exact hB i k r x) := by
  unfold inducedTelescopeHomotopy inducedTelescopeMap
  rw [Telescope.mapHomotopy_at]
  apply Telescope.hom_ext
  intro k n s x
  exact congrArg (fun y ↦ Telescope.cylinder (stage E' V' a' b')
    (transition E' V' a' b') k n (s, y))
      (congrArg (fun m ↦ m.map k x) (stageHomotopy_at E V a b E' V' a' b'
        d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB r n))

variable (f : ∀ n, E n ⟶ E (n + 1)) (f' : ∀ n, E' n ⟶ E' (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ b n))
    (H' : ∀ n, Homotopy (a' n) (f' n ≫ b' n))
    (hFactor : ∀ n k r s x, (HV n).level k (r, (H n).level k (s, x)) =
      (H' n).level k (s, (HE n).level k (r, x)))

include hFactor in
/-- The original factorization clock commutes with the separate whole-family clock. -/
theorem stageHomotopy_comparisonTrack (n k : ℕ) (r s : unitInterval)
    (x : (E n).space k) :
    (stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB
      (n + 1)).level k (r, (comparisonTrack E V a b f H n).level k (s, x)) =
        (comparisonTrack E' V' a' b' f' H' n).level k (s, (HE n).level k (r, x)) := by
  change ((stageHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
    ha₀ hb₀ ha₁ hb₁ HE HV hA hB (n + 1)).at r).map k _ = _
  rw [stageHomotopy_at]
  exact comparisonTrack_naturality E V a b E' V' a' b'
    (fun i ↦ (HE i).at r) (fun i ↦ (HV i).at r) _ _ f f' H H'
    (fun i j s y ↦ hFactor i j r s y) n k s x

variable (hd₀ : ∀ n, d₀ n ≫ f' n = f n ≫ d₀ (n + 1))
    (hd₁ : ∀ n, d₁ n ≫ f' n = f n ≫ d₁ (n + 1))
    (hF : ∀ n k r x, (f' n).map k ((HE n).level k (r, x)) =
      (HE (n + 1)).level k (r, (f n).map k x))

include hFactor in
/-- The actual comparison of telescopes preserves the entire specified input family. -/
theorem telescopeMap_homotopy (k : ℕ) (r : unitInterval)
    (q : (Telescope.prespectrum E f).space k) :
    (inducedTelescopeHomotopy E V a b E' V' a' b' d₀ d₁ v₀ v₁
      ha₀ hb₀ ha₁ hb₁ HE HV hA hB).level k (r, (telescopeMap E V a b f H).map k q) =
      (telescopeMap E' V' a' b' f' H').map k
        ((Telescope.mapHomotopy E f E' f' d₀ d₁ hd₀ hd₁ HE hF).level k (r, q)) := by
  have h := telescopeMap_naturality E V a b E' V' a' b'
    (fun i ↦ (HE i).at r) (fun i ↦ (HV i).at r)
    (fun i ↦ by apply Hom.ext; funext j; ext x; exact hA i j r x)
    (fun i ↦ by apply Hom.ext; funext j; ext x; exact hB i j r x)
    f f' H H' (fun i j s x ↦ hFactor i j r s x)
    (fun i ↦ by apply Hom.ext; funext j; ext x; exact hF i j r x)
  rw [← Telescope.mapHomotopy_at E f E' f' d₀ d₁ hd₀ hd₁ HE hF r,
    ← inducedTelescopeHomotopy_at E V a b E' V' a' b'
      d₀ d₁ v₀ v₁ ha₀ hb₀ ha₁ hb₁ HE HV hA hB r] at h
  exact congrArg (fun m ↦ m.map k q) h.symm

end Topology.LoopPrespectrum.ZigzagSequentialization
