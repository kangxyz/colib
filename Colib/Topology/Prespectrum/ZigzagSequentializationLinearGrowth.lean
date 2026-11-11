/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentializationStable
public import Colib.Topology.Prespectrum.PushoutLinearExcision

/-!
# Discharging sequentialization excision from original finite-stage growth

All-point linear growth passes through every original finite pushout stage. A monotone
stage-dependent offset suffices; no uniform bound over the tower is required. The existing
linear excision theorems then discharge both row-excision premises of the actual stable
telescope comparison. Only growth, T1 separation and point HEP of the original zigzag
vertices, stability of the original unit legs, and the whole factorization tracks remain.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization

private theorem linearGrowth_mono (E : LoopPrespectrum.{u}) {c c' : ℕ} (hc : c ≤ c')
    (hπ : ∀ n (x : E.space (n + c + 2)) k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x)) :
    ∀ n (x : E.space (n + c' + 2)) k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c' + 2)) x) := by
  intro n
  have h := hπ (n + (c' - c))
  rw [show n + (c' - c) + c + 2 = n + c' + 2 by omega] at h
  exact fun x k hk ↦ h x k (by omega)

variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)
    (c : ℕ → ℕ) (hc : Monotone c)
    (hE : ∀ n k, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((E n).point k))))
    (hV : ∀ n k, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((V n).point k))))
    (hπE : ∀ i n (x : (E i).space (n + c i + 2)) k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k ((E i).space (n + c i + 2)) x))
    (hπV : ∀ i n (x : (V i).space (n + c (i + 1) + 2)) k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k ((V i).space (n + c (i + 1) + 2)) x))

include hE hV in
private theorem stage_pointHEP (i m : ℕ) (hm : 1 ≤ m) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((stage E V a b i).point m))) := by
  have h := stage_point_homotopyExtensionProperty E V a b
    (fun i k ↦ hE i (k + 1)) (fun i k ↦ hV i (k + 1)) i (m - 1)
  rw [show m - 1 + 1 = m by omega] at h
  exact h

include hc hE hV hπE hπV in
/-- Every original finite pushout stage retains its monotone linear-growth offset. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationLinearGrowth.lean:61"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem stage_linearGrowth : ∀ i n (x : (stage E V a b i).space (n + c i + 2)) k,
    k < n + 2 → Subsingleton (HomotopyGroup.Pi k ((stage E V a b i).space (n + c i + 2)) x) := by
  intro i
  induction i with
  | zero => exact hπE 0
  | succ i ih =>
    cases i with
    | zero => exact hπV 0
    | succ i =>
      intro n x k hk
      have hle : c (i + 1) ≤ c (i + 1 + 1) := hc (Nat.le_succ _)
      have hA := linearGrowth_mono (E (i + 1)) hle (hπE (i + 1))
      have hB := linearGrowth_mono (stage E V a b (i + 1)) hle ih
      exact HomotopyPushout.homotopyGroup_subsingleton
        (comparison E V a b (i + 1)) (a (i + 1)) _ n
        (hE (i + 1) _) (stage_pointHEP E V a b hE hV (i + 1) _ (by omega))
        (hV (i + 1) _) (hA n) (hB n) (hπV (i + 1) n) x k hk

include hc hE hV hπE hπV in
/-- Original finite-stage growth proves excision for every original attaching comparison. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationLinearGrowth.lean:81"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem comparison_coneFiber_isStableEquivalence (i : ℕ) :
    IsStableEquivalence (mappingConeFiberComparison (comparison E V a b (i + 1))) :=
  mappingConeFiberComparison_isStableEquivalence_of_linearGrowth
    (comparison E V a b (i + 1)) (c (i + 1))
    (fun n ↦ hE (i + 1) _) (fun n ↦ stage_pointHEP E V a b hE hV (i + 1) _ (by omega))
    (hπE (i + 1)) (stage_linearGrowth E V a b c hc hE hV hπE hπV (i + 1))

include hc hE hV hπE hπV in
/-- The same growth proves excision for the original right inclusion of every new pushout. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationLinearGrowth.lean:90"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem inr_coneFiber_isStableEquivalence (i : ℕ) :
    IsStableEquivalence (mappingConeFiberComparison
      (HomotopyPushout.inr (comparison E V a b (i + 1)) (a (i + 1)))) := by
  have hle : c (i + 1) ≤ c (i + 1 + 1) := hc (Nat.le_succ _)
  exact HomotopyPushout.inr_coneFiber_isStableEquivalence_of_linearGrowth
    (comparison E V a b (i + 1)) (a (i + 1)) (c (i + 1 + 1))
    (fun n ↦ hE (i + 1) _) (fun n ↦ stage_pointHEP E V a b hE hV (i + 1) _ (by omega))
    (fun n ↦ hV (i + 1) _)
    (linearGrowth_mono (E (i + 1)) hle (hπE (i + 1)))
    (linearGrowth_mono (stage E V a b (i + 1)) hle
      (stage_linearGrowth E V a b c hc hE hV hπE hπV (i + 1))) (hπV (i + 1))

variable (hb : ∀ n, IsStableEquivalence (b n))
    (f : ∀ n, E n ⟶ E (n + 1)) (H : ∀ n, Homotopy (a n) (f n ≫ b n))
    [∀ n k, T1Space ((E n).space k)] [∀ n k, T1Space ((V n).space k)]

include hc hE hV hπE hπV hb in
/-- Finite-stage growth discharges the genuine excision inputs of the actual telescope map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationLinearGrowth.lean:108"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem telescopeMap_isStableEquivalence_of_linearGrowth :
    IsStableEquivalence (telescopeMap E V a b f H) :=
  telescopeMap_isStableEquivalence_of_excision E V a b
    (fun i k ↦ hE i (k + 1)) (fun i k ↦ hV i (k + 1)) hb
    (comparison_coneFiber_isStableEquivalence E V a b c hc hE hV hπE hπV)
    (inr_coneFiber_isStableEquivalence E V a b c hc hE hV hπE hπV) f H

end Topology.LoopPrespectrum.ZigzagSequentialization
