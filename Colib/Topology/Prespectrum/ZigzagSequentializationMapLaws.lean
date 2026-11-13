/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentializationNaturality

/-!
# Identity, composition and zero laws for actual recursive zigzag maps

The original strict maps act on all three generators of every actual reduced homotopy
pushout. Their recursive stage maps preserve identities,
composition and zero maps strictly. In particular a whole family ending at zero may use
this literal endpoint law without choosing a nullhomotopic replacement.
-/
/-!
Implementation provenance: adapted from Quillen at
`ZigzagSequentializationMapLaws.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)

/-- The original recursive stage map of identity input maps is the identity. -/
@[simp] theorem stageMap_id (n : ℕ) :
    stageMap E V a b E V a b (fun i ↦ 𝟙 (E i)) (fun i ↦ 𝟙 (V i))
      (fun i ↦ by simp) (fun i ↦ by simp) n = 𝟙 (stage E V a b n) := by
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
                (comparison E V a b (n + 1)) (a (n + 1)) k)
                  (congrArg (fun m ↦ m.map k x) ih)
          | inr x => rfl
        | inr z => rfl

variable (E' V' : ℕ → LoopPrespectrum.{u})
    (a' : ∀ n, E' n ⟶ V' n) (b' : ∀ n, E' (n + 1) ⟶ V' n)

/-- Original zero input maps induce the literal zero recursive stage map. -/
@[simp] theorem stageMap_zero (n : ℕ) :
    stageMap E V a b E' V' a' b' (fun i ↦ zeroHom (E i) (E' i))
      (fun i ↦ zeroHom (V i) (V' i))
      (fun i ↦ by apply Hom.ext; funext k; ext _x; exact (a' i).map_point k |>.symm)
      (fun i ↦ by apply Hom.ext; funext k; ext _x; exact (b' i).map_point k |>.symm) n =
        zeroHom (stage E V a b n) (stage E' V' a' b' n) := by
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
          | inr x => exact HomotopyPushout.right_point _ _ k
        | inr z => exact HomotopyPushout.cylinder_point _ _ k z.1

variable (d : ∀ n, E n ⟶ E' n) (v : ∀ n, V n ⟶ V' n)
    (ha : ∀ n, a n ≫ v n = d n ≫ a' n)
    (hb : ∀ n, b n ≫ v n = d (n + 1) ≫ b' n)
    (E'' V'' : ℕ → LoopPrespectrum.{u})
    (a'' : ∀ n, E'' n ⟶ V'' n) (b'' : ∀ n, E'' (n + 1) ⟶ V'' n)
    (d' : ∀ n, E' n ⟶ E'' n) (v' : ∀ n, V' n ⟶ V'' n)
    (ha' : ∀ n, a' n ≫ v' n = d' n ≫ a'' n)
    (hb' : ∀ n, b' n ≫ v' n = d' (n + 1) ≫ b'' n)

/-- Recursive original stage maps preserve the exact composite of input zigzag maps. -/
@[simp] theorem stageMap_comp (n : ℕ) :
    stageMap E V a b E' V' a' b' d v ha hb n ≫
      stageMap E' V' a' b' E'' V'' a'' b'' d' v' ha' hb' n =
        stageMap E V a b E'' V'' a'' b'' (fun i ↦ d i ≫ d' i) (fun i ↦ v i ≫ v' i)
          (fun i ↦ by rw [← Category.assoc, ha, Category.assoc, ha', Category.assoc])
          (fun i ↦ by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]) n := by
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
                (comparison E'' V'' a'' b'' (n + 1)) (a'' (n + 1)) k)
                  (congrArg (fun m ↦ m.map k x) ih)
          | inr x => rfl
        | inr z => rfl

end Topology.LoopPrespectrum.ZigzagSequentialization
