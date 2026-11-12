/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sets.Opens

/-!
# The standard density filtration of opens

An open belongs to the standard density filtration in degree `d` if each
point outside it starts a chain of `d` strict generizations. The predicate
uses coheight in the native specialization order.

See [Voevodsky, §2, pp. 4–5](https://arxiv.org/abs/0805.4576).
-/

@[expose] public section

open Order Topology TopologicalSpace

namespace TopologicalSpace.Opens

attribute [local instance] specializationOrder

universe u v

variable {X : Type u} [TopologicalSpace X] [T0Space X]
variable {U V : Opens X} {d e : ℕ}

/-- Each point outside the open has coheight at least the specified degree. -/
def IsInStandardDensity (U : Opens X) (d : ℕ) : Prop :=
  ∀ x : X, x ∉ U → (d : ℕ∞) ≤ coheight x

/-- Coheight gives the same predicate as the strict generization chains in
the standard density filtration. -/
theorem isInStandardDensity_iff_exists_series (U : Opens X) (d : ℕ) :
    U.IsInStandardDensity d ↔
      ∀ x : X, x ∉ U → ∃ p : LTSeries X, p.head = x ∧ p.length = d := by
  constructor
  · intro h x hx
    exact exists_series_of_le_coheight x (h x hx)
  · intro h x hx
    obtain ⟨p, hhead, hlength⟩ := h x hx
    simpa only [hhead, hlength] using (length_le_coheight_head (p := p))

/-- Every open belongs to degree zero of the standard density filtration. -/
theorem isInStandardDensity_zero (U : Opens X) : U.IsInStandardDensity 0 :=
  fun _ _ ↦ bot_le

/-- The whole space belongs to every degree of the standard density filtration. -/
theorem isInStandardDensity_top (d : ℕ) : (⊤ : Opens X).IsInStandardDensity d := by
  intro x hx
  exact (hx (by simp)).elim

/-- Enlarging the open preserves membership in the standard density filtration. -/
theorem IsInStandardDensity.mono (hU : U.IsInStandardDensity d) (hUV : U ≤ V) :
    V.IsInStandardDensity d :=
  fun x hx ↦ hU x fun hxU ↦ hx (hUV hxU)

/-- Membership in the standard density filtration descends in degree. -/
theorem IsInStandardDensity.of_le (hU : U.IsInStandardDensity e) (hde : d ≤ e) :
    U.IsInStandardDensity d :=
  fun x hx ↦ (ENat.natCast_le_natCast.mpr hde).trans (hU x hx)

/-- The degreewise standard density filtration is closed under intersection. -/
theorem IsInStandardDensity.inf (hU : U.IsInStandardDensity d)
    (hV : V.IsInStandardDensity d) : (U ⊓ V).IsInStandardDensity d := by
  intro x hx
  change ¬ (x ∈ U ∧ x ∈ V) at hx
  by_cases hxU : x ∈ U
  · exact hV x fun hxV ↦ hx ⟨hxU, hxV⟩
  · exact hU x hxU

/-- Restriction along an open embedding preserves the standard density
filtration. -/
theorem IsInStandardDensity.comap [QuasiSober X] {Y : Type v}
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] {f : C(Y, X)}
    (hU : U.IsInStandardDensity d) (hf : IsOpenEmbedding f) :
    (Opens.comap f U).IsInStandardDensity d := by
  intro y hy
  have h := hU (f y) hy
  rwa [Topology.IsOpenEmbedding.coheight_eq f hf] at h

/-- Composing two open inclusions in the same degree of the filtration
preserves that degree. -/
theorem IsInStandardDensity.image_subtypeVal [QuasiSober X]
    (hU : U.IsInStandardDensity d) {W : Opens U} (hW : W.IsInStandardDensity d) :
    (⟨Subtype.val '' (W : Set U), U.isOpenEmbedding'.isOpenMap _ W.isOpen⟩ :
      Opens X).IsInStandardDensity d := by
  let : QuasiSober U := U.isOpenEmbedding'.quasiSober
  intro x hx
  by_cases hxU : x ∈ U
  · let y : U := ⟨x, hxU⟩
    have hy : y ∉ W := fun hyW ↦ hx ⟨y, hyW, rfl⟩
    change (d : ℕ∞) ≤ coheight ((Subtype.val : U → X) y)
    rw [Topology.IsOpenEmbedding.coheight_eq _ U.isOpenEmbedding']
    exact hW y hy
  · exact hU x hxU

/-- Above the topological Krull dimension the standard density filtration
contains only the whole space. -/
theorem IsInStandardDensity.eq_top_of_topologicalKrullDim_lt [QuasiSober X]
    (hU : U.IsInStandardDensity d) (hd : topologicalKrullDim X < d) : U = ⊤ := by
  refine le_antisymm le_top fun x _ ↦ ?_
  by_contra hx
  have he : krullDim X = topologicalKrullDim X :=
    krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)).symm
  have hle : (d : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    rw [← he]
    exact (WithBot.coe_le_coe.mpr (hU x hx)).trans (coheight_le_krullDim x)
  exact (not_lt_of_ge hle) hd

end TopologicalSpace.Opens
