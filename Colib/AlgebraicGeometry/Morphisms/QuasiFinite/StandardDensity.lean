/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Dimension.StandardDensity
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantOpenBetween

/-!
# Density and closed images of locally quasi-finite morphisms

Discrete fibers preserve strict generizations. The complement of the closure of the
image of the complement of a dense open therefore has the same density index.
If the bad image lies in another open, a point outside that open needs an additional
strict generization to reach the bad image.

See [Voevodsky, Lemma 2.8 and Proposition 2.9](https://arxiv.org/pdf/0805.4576#page=6).
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] specializationOrder

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A locally quasi-finite morphism strictly preserves the specialization order. -/
theorem strictMono_specialization [LocallyQuasiFinite f] : StrictMono (fun x : X ↦ f x) := by
  intro x y hxy
  have h : y ⤳ x := le_of_lt hxy
  exact lt_of_le_of_ne (h.map f.continuous) fun heq ↦
    (ne_of_lt hxy) ((f.isDiscrete_preimage_singleton (f x)).eq_of_specializes h heq.symm rfl).symm

/-- The largest open of the target whose preimage is contained in `V`. -/
def densityImageComplement (V : X.Opens) : Y.Opens :=
  ⟨(closure (f.base '' (V : Set X)ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩

/-- The preimage of the open avoiding the closed bad image is contained in the original open. -/
theorem preimage_densityImageComplement_le (V : X.Opens) :
    f ⁻¹ᵁ f.densityImageComplement V ≤ V := by
  intro x hx
  by_contra h
  exact hx (subset_closure ⟨x, h, rfl⟩)

variable [QuasiCompact f] [LocallyQuasiFinite f]

/-- Deleting the closure of the bad image preserves the standard density index. -/
theorem isInStandardDensity_densityImageComplement {V : X.Opens} {d : ℕ}
    (hV : V.IsInStandardDensity d) : (f.densityImageComplement V).IsInStandardDensity d := by
  intro y hy
  have hy' : y ∈ closure (f.base '' (V : Set X)ᶜ) := by
    simpa only [densityImageComplement, Opens.mem_mk, Set.mem_compl_iff, not_not] using hy
  obtain ⟨x, hx, hxy⟩ := exists_specializes_mem_of_mem_closure_image f V.isOpen.isClosed_compl hy'
  have h := coheight_le_coheight_apply_of_strictMono _ f.strictMono_specialization x
  exact (hV x hx).trans (h.trans (coheight_anti (show y ≤ f x from hxy)))

/-- Outside an open containing the image, there is an additional strict generization
before a point can reach the bad image. -/
theorem isInStandardDensity_sup_densityImageComplement {V : X.Opens} {d : ℕ}
    (hV : V.IsInStandardDensity d) (O : Y.Opens) (hO : Set.range f ⊆ O) :
    (O ⊔ f.densityImageComplement V).IsInStandardDensity (d + 1) := by
  intro y hy
  have hyO : y ∉ O := fun h ↦ hy ((le_sup_left : O ≤ O ⊔ f.densityImageComplement V) h)
  have hyD : y ∉ f.densityImageComplement V := fun h ↦
    hy ((le_sup_right : f.densityImageComplement V ≤ O ⊔ f.densityImageComplement V) h)
  have hy' : y ∈ closure (f.base '' (V : Set X)ᶜ) := by
    simpa only [densityImageComplement, Opens.mem_mk, Set.mem_compl_iff, not_not] using hyD
  obtain ⟨x, hx, hxy⟩ := exists_specializes_mem_of_mem_closure_image f V.isOpen.isClosed_compl hy'
  have hlt : y < f x := lt_of_le_of_ne hxy (fun heq ↦ hyO (heq.symm ▸ hO ⟨x, rfl⟩))
  have hx' : (d : ℕ∞) ≤ coheight (f x) :=
    (hV x hx).trans (coheight_le_coheight_apply_of_strictMono _ f.strictMono_specialization x)
  calc
    ((d + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + 1 := by simp
    _ ≤ coheight (f x) + 1 := by gcongr
    _ ≤ coheight y := coheight_add_one_le hlt

end AlgebraicGeometry.Scheme.Hom
