/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.PowerCutExterior
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Admissibility
import Colib.AlgebraicGeometry.Correspondences.Additive.Ext

/-!
# The signed cut of the inner exterior identity

The comparison adds the actual prime equalities with their original
signs. A common exponent covers the full finite support.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme SmoothSite
open AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "F" => parameterProduct T

private def torusInnerExtensionAddHom {X Y : Cor k} :
    ((F).obj X ⟶ (F).obj Y) →+ ((F).obj ((F).obj X) ⟶ (F).obj ((F).obj Y)) :=
  (Preadditive.rightComp ((F).obj ((F).obj X)) (torusDoubleSwap k Y)).comp
    ((Preadditive.leftComp ((F).obj ((F).obj Y)) (torusDoubleSwap k X)).comp (F).mapAddHom)

private theorem torusInnerExtensionAddHom_apply {X Y : Cor k} (a : (F).obj X ⟶ (F).obj Y) :
    torusInnerExtensionAddHom k a = torusInnerExtension k a := by
  change (torusDoubleSwap k X ≫ (F).map a) ≫ torusDoubleSwap k Y = _
  exact Category.assoc _ _ _

variable {X Y : SmoothSite (Spec (.of k))}

local notation3 (prettyPrint := false) "gx" => (G(X)).hom
local notation3 (prettyPrint := false) "gy" => (G(Y)).hom
local notation3 (prettyPrint := false) "gxx" => (G(G(X))).hom
local notation3 (prettyPrint := false) "gyy" => (G(G(Y))).hom

/-- The inner extension preserves each original signed prime coefficient. -/
theorem torusInnerExtension_single (w : pullback (C := Scheme) gx gy)
    (hw : IsFiniteCorrespondencePoint gx gy w) (m : ℤ) :
    torusInnerExtension k (singleFiniteCorrespondence gx gy w hw m) =
      singleFiniteCorrespondence gxx gyy (torusInnerExtensionPrimePoint k X Y w hw)
        (torusInnerExtensionPrimePoint_admissible k X Y w hw) m := by
  have h₁ :
      torusInnerExtension k (singleFiniteCorrespondence gx gy w hw 1) =
        singleFiniteCorrespondence gxx gyy (torusInnerExtensionPrimePoint k X Y w hw)
          (torusInnerExtensionPrimePoint_admissible k X Y w hw) 1 :=
    Subtype.ext (torusInnerExtensionPrime_val k X Y w hw)
  rw [← torusInnerExtensionAddHom_apply, singleFiniteCorrespondence_eq_zsmul, map_zsmul,
    torusInnerExtensionAddHom_apply, h₁, ← singleFiniteCorrespondence_eq_zsmul]

set_option maxHeartbeats 300000 in
-- The finite sum is typed in the two actual correspondence groups.
/-- If the original signed support and its actual inner images admit the
cuts, the inner extension admits them and its cut is the exterior identity
of the original cut. -/
theorem torusPowerCut_innerExtension_of_support
    (a : Cor.mk (G(X)) ⟶ Cor.mk (G(Y))) (n : ℕ)
    (ha : a ∈ torusPowerCutDomain k X Y n)
    (himage : ∀ w (hw : IsFiniteCorrespondencePoint gx gy w), a.val w ≠ 0 →
      TorusPowerCutAdmissibleAt k (G(X)) (G(Y)) (torusInnerExtensionPrimePoint k X Y w hw) n) :
    let b : Cor.mk (G(G(X))) ⟶ Cor.mk (G(G(Y))) :=
      torusInnerExtension k (X := Cor.mk X) (Y := Cor.mk Y) a
    ∃ ha' : b ∈ torusPowerCutDomain k (G(X)) (G(Y)) n,
      torusPowerCut k (G(X)) (G(Y)) n ⟨b, ha'⟩ =
        (F).map (torusPowerCut k X Y n ⟨a, ha⟩) := by
  classical
  let b : Cor.mk (G(G(X))) ⟶ Cor.mk (G(G(Y))) :=
    torusInnerExtension k (X := Cor.mk X) (Y := Cor.mk Y) a
  change ∃ ha' : b ∈ torusPowerCutDomain k (G(X)) (G(Y)) n, _
  let S := a.property.1.toFinset
  let hne (w : S) : a.val w.val ≠ 0 := by
    simpa only [S, Set.Finite.mem_toFinset, Function.locallyFinsuppWithin.support,
      Function.mem_support] using w.property
  let hw (w : S) := a.property.2 w.val (hne w)
  let w' (w : S) := torusInnerExtensionPrimePoint k X Y w.val (hw w)
  let hw' (w : S) := torusInnerExtensionPrimePoint_admissible k X Y w.val (hw w)
  let h₀ (w : S) := (mem_torusPowerCutDomain_iff k X Y n a).mp ha w.val (hne w)
  let h₁ (w : S) := himage w.val (hw w) (hne w)
  let s (w : S) : Cor.mk (G(X)) ⟶ Cor.mk (G(Y)) :=
    singleFiniteCorrespondence gx gy w.val (hw w) (a.val w.val)
  let s' (w : S) : Cor.mk (G(G(X))) ⟶ Cor.mk (G(G(Y))) :=
    singleFiniteCorrespondence gxx gyy (w' w) (hw' w) (a.val w.val)
  let d (w : S) : torusPowerCutDomain k X Y n :=
    ⟨s w, single_mem_torusPowerCutDomain k X Y w.val n (hw w) (h₀ w) _⟩
  let d' (w : S) : torusPowerCutDomain k (G(X)) (G(Y)) n :=
    ⟨s' w, single_mem_torusPowerCutDomain k (G(X)) (G(Y)) (w' w) n (hw' w) (h₁ w) _⟩
  have hsum : a = ∑ w : S, s w := finiteCorrespondence_eq_sum_signedSingles gx gy a
  have hsum' : b = ∑ w : S, s' w := by
    change torusInnerExtension k (X := Cor.mk X) (Y := Cor.mk Y) a = _
    rw [← torusInnerExtensionAddHom_apply, hsum, map_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [torusInnerExtensionAddHom_apply]
    exact torusInnerExtension_single k (X := X) (Y := Y) w.val (hw w) (a.val w.val)
  have hm : b ∈ torusPowerCutDomain k (G(X)) (G(Y)) n := by
    rw [hsum']
    exact AddSubgroup.sum_mem _ fun w _ => (d' w).property
  refine ⟨hm, ?_⟩
  have H : (⟨a, ha⟩ : torusPowerCutDomain k X Y n) = ∑ w : S, d w := by
    apply Subtype.ext
    change a = (torusPowerCutDomain k X Y n).subtype (∑ w : S, d w)
    rw [map_sum]
    exact hsum
  have H' : (⟨b, hm⟩ : torusPowerCutDomain k (G(X)) (G(Y)) n) =
      ∑ w : S, d' w := by
    apply Subtype.ext
    change b = (torusPowerCutDomain k (G(X)) (G(Y)) n).subtype (∑ w : S, d' w)
    rw [map_sum]
    exact hsum'
  rw [H, H']
  simp only [map_sum, Functor.map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [show torusPowerCut k X Y n (d w) =
      a.val w.val • torusPowerCutPrime k X Y w.val n (h₀ w) from
    torusPowerCut_single k X Y w.val n (hw w) (h₀ w) _,
    show torusPowerCut k (G(X)) (G(Y)) n (d' w) =
      a.val w.val • torusPowerCutPrime k (G(X)) (G(Y)) (w' w) n (h₁ w) from
    torusPowerCut_single k (G(X)) (G(Y)) (w' w) n (hw' w) (h₁ w) _,
    Functor.map_zsmul]
  exact congrArg (a.val w.val • ·)
    (torusPowerCutPrime_innerExtension k X Y w.val (hw w) n (h₀ w) (h₁ w))

set_option maxHeartbeats 360000 in
-- Keep the retained support image explicit during the finite-family bound.
/-- The inner exterior identity comparison has a common eventual exponent
on the actual signed support. -/
theorem exists_torusPowerCut_innerExtension (a : Cor.mk (G(X)) ⟶ Cor.mk (G(Y))) :
    let b : Cor.mk (G(G(X))) ⟶ Cor.mk (G(G(Y))) :=
      torusInnerExtension k (X := Cor.mk X) (Y := Cor.mk Y) a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      a ∈ torusPowerCutDomain k X Y n ∧
      b ∈ torusPowerCutDomain k (G(X)) (G(Y)) n ∧
      ∀ (ha : a ∈ torusPowerCutDomain k X Y n)
        (ha' : b ∈ torusPowerCutDomain k (G(X)) (G(Y)) n),
        torusPowerCut k (G(X)) (G(Y)) n ⟨b, ha'⟩ =
          (F).map (torusPowerCut k X Y n ⟨a, ha⟩) := by
  dsimp only
  classical
  obtain ⟨N₀, h₀⟩ := exists_mem_torusPowerCutDomain k X Y a
  let S := a.property.1.toFinset
  let hw (w : S) : IsFiniteCorrespondencePoint gx gy w.val :=
    a.property.2 w.val (a.property.1.mem_toFinset.mp w.property)
  choose b hb using fun w : S =>
    exists_torusPowerCutAdmissibleAt k (G(X)) (G(Y))
      (torusInnerExtensionPrimePoint k X Y w.val (hw w))
      (torusInnerExtensionPrimePoint_admissible k X Y w.val (hw w))
  let N₁ := Finset.univ.sup b
  refine ⟨max N₀ N₁, fun n hn => ?_⟩
  have ha := h₀ n ((le_max_left _ _).trans hn)
  have hi (w : pullback (C := Scheme) gx gy) (hW : IsFiniteCorrespondencePoint gx gy w)
      (hm : a.val w ≠ 0) :
      TorusPowerCutAdmissibleAt k (G(X)) (G(Y)) (torusInnerExtensionPrimePoint k X Y w hW) n := by
    let w' : S := ⟨w, a.property.1.mem_toFinset.mpr hm⟩
    have hle : b w' ≤ N₁ := Finset.le_sup (Finset.mem_univ w')
    exact hb w' n (hle.trans ((le_max_right _ _).trans hn))
  obtain ⟨ha', he⟩ := torusPowerCut_innerExtension_of_support k (X := X) (Y := Y) a n ha hi
  exact ⟨ha, ha', fun _ _ => he⟩

end AlgebraicGeometry.PresheafWithTransfers
