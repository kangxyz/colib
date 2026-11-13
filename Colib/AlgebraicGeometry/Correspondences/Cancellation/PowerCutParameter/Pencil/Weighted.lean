/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.SignedEndpoint
import Colib.AlgebraicGeometry.Correspondences.Additive.Ext

/-!
# A correspondence between the two large power cuts

For an actual finite correspondence, one bound controls the pencil on
every point of its finite support. The signed sum of the individual
pencils keeps the original coefficient at every support point. Its two
graph faces are the two large-exponent power cuts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Chow
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "XG" => (product X T)
local notation "YG" => (product Y T)
local notation "B" => (product X (additiveGroupObject Sₖ))
local notation "φ(" a ")" => nativeAffineSection (CommRingCat.of k) X a

/-- Every two sufficiently large power cuts are the graph faces of the
same actual finite correspondence over the affine-line cylinder. -/
@[colib_tag "COL-1043", colib_ref "Voevodsky2010Cancellation" "Remark 4.2, p. 680"
  "adaptation" "The original signed cut cycles are the two polynomial faces"]
theorem exists_torusPowerCut_pencil (c : Cor.mk XG ⟶ Cor.mk YG) :
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      ∃ (hm : c ∈ torusPowerCutDomain k X Y m) (hn : c ∈ torusPowerCutDomain k X Y n)
        (H : Cor.mk B ⟶ Cor.mk Y),
        (graphFunctor k).map (φ(0)) ≫ H = torusPowerCut k X Y n ⟨c, hn⟩ ∧
        (graphFunctor k).map (φ(1)) ≫ H = torusPowerCut k X Y m ⟨c, hm⟩ := by
  classical
  let I := c.property.1.toFinset
  have hmem (z : I) : c.val z.val ≠ 0 := c.property.1.mem_toFinset.mp z.property
  let hz (z : I) := c.property.2 z.val (hmem z)
  let u₀ (z : I) := torusSupportCoordinate k (torusPowerCutTarget k X Y z.val)
  choose L hL using fun z : I => exists_torusPowerCutPencilPrime_endpoints k X Y z.val (hz z)
  refine ⟨Finset.univ.sup L, fun m n hm hn => ?_⟩
  have hfaces (z : I) := hL z m n ((Finset.le_sup (Finset.mem_univ z)).trans hm)
    ((Finset.le_sup (Finset.mem_univ z)).trans hn)
  choose h₁ h₂ hP hface using hfaces
  have hdom (l : ℕ) (hl : ∀ z : I, TorusPowerCutAdmissibleAt k X Y z.val l) :
      c ∈ torusPowerCutDomain k X Y l := by
    apply (mem_torusPowerCutDomain_iff k X Y l c).mpr
    intro z h
    exact hl ⟨z, c.property.1.mem_toFinset.mpr h⟩
  have hcut (l : ℕ) (hl : ∀ z : I, TorusPowerCutAdmissibleAt k X Y z.val l) :
      torusPowerCut k X Y l ⟨c, hdom l hl⟩ =
        ∑ z : I, c.val z.val • torusPowerCutPrime k X Y z.val l (hl z) := by
    let s (z : I) : torusPowerCutDomain k X Y l :=
      ⟨singleFiniteCorrespondence (XG).hom (YG).hom z.val (hz z) (c.val z.val),
        single_mem_torusPowerCutDomain k X Y z.val l (hz z) (hl z) (c.val z.val)⟩
    have hc : (⟨c, hdom l hl⟩ : torusPowerCutDomain k X Y l) = ∑ z : I, s z := by
      apply Subtype.ext
      change c = (torusPowerCutDomain k X Y l).subtype _
      rw [map_sum]
      exact finiteCorrespondence_eq_sum_signedSingles (XG).hom (YG).hom c
    rw [hc, map_sum]
    apply Finset.sum_congr rfl
    intro z _
    exact torusPowerCut_single k X Y z.val l (hz z) (hl z) (c.val z.val)
  let H : Cor.mk B ⟶ Cor.mk Y :=
    ∑ z : I, c.val z.val • torusPowerCutPencilPrime k X Y z.val (u₀ z) (m + 1) (n + 1) (hP z)
  refine ⟨hdom m h₁, hdom n h₂, H, ?_, ?_⟩
  · rw [hcut n h₂]
    simp only [H, Preadditive.comp_sum, Preadditive.comp_zsmul]
    apply Finset.sum_congr rfl
    intro z _
    rw [(hface z).1]
  · rw [hcut m h₁]
    simp only [H, Preadditive.comp_sum, Preadditive.comp_zsmul]
    apply Finset.sum_congr rfl
    intro z _
    rw [(hface z).2]

end AlgebraicGeometry.Cor
