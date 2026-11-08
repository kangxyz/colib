/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg

/-!
# Finite pushforward of native algebraic cycles

This is a new, source-only reconstruction, not a recovery of the historical file.
It has not been elaborated or compiled. It specializes the existing native
`AlgebraicGeometry.AlgebraicCycle.map` to constant weights for a finite morphism.
Thus every coefficient is the sum over the entire fibre, with the actual residue
field degree. Distinct source points are allowed to have the same image.

The native cycle type and its local-finiteness proof are reused unchanged.
Composition uses the native weighted pushforward composition theorem and
multiplicativity of the residue degree. No Chow quotient is used here.

The correspondence-specific adapter is intentionally not asserted here: one must
prove that the integral closed image of every relevant support is finite over the
source and dominates an irreducible source component. In particular, an incidence
adapter must retain the separate component-image hypothesis, rather than inferring
nonverticality from finiteness of the incidence projection.

## References

* Stacks Project, Tag 02R4: proper pushforward and its residue-degree coefficient.
* Stacks Project, Tag 02R5: functoriality of proper pushforward.
* Stacks Project, Tag 030H: degrees in towers of fields.
* Mathlib `AlgebraicGeometry/AlgebraicCycle/Basic.lean`, revision
  `56a005855ea17e0b0958f73ec801ae140b0a1679`.
* Stacks `Chow/ProperPushforwardChow/Functoriality.lean` and
  `Chow/ProperPushforwardPrincipal/ResidueTrdeg.lean`, revision
  `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable {X Y Z : Scheme.{u}}

/-- Finite pushforward, on the existing group of native integral-coefficient cycles.
Constant weights do not discard any point: the coefficient is its residue degree. -/
def finiteCyclePushforward (f : X ⟶ Y) [IsFinite f] :
    AlgebraicCycle X ℤ →+ AlgebraicCycle Y ℤ where
  toFun := AlgebraicCycle.map f (fun _ : X ↦ (0 : ℕ)) (fun _ : Y ↦ (0 : ℕ))
  map_zero' := by
    apply Function.locallyFinsuppWithin.ext
    intro y
    simp [AlgebraicCycle.map, Function.locallyFinsupp.map, AlgebraicCycle.mapCoeff]
  map_add' a b := by
    apply Function.locallyFinsuppWithin.ext
    intro y
    have hfin := f.finite_preimage_singleton y
    simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply,
      AlgebraicCycle.mapCoeff, ite_true, Function.locallyFinsuppWithin.coe_add,
      Pi.add_apply, add_mul]
    exact finsum_mem_add_distrib' (hfin.subset Set.inter_subset_left)
      (hfin.subset Set.inter_subset_left)

/-- The construction is the existing native cycle map, not a second cycle model. -/
theorem finiteCyclePushforward_eq_map (f : X ⟶ Y) [IsFinite f]
    (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward f c =
      AlgebraicCycle.map f (fun _ : X ↦ (0 : ℕ)) (fun _ : Y ↦ (0 : ℕ)) c :=
  rfl

/-- All points of a fibre contribute, including coincident images of different supports. -/
theorem finiteCyclePushforward_apply (f : X ⟶ Y) [IsFinite f]
    (c : AlgebraicCycle X ℤ) (y : Y) :
    finiteCyclePushforward f c y =
      ∑ᶠ x ∈ f.base ⁻¹' {y}, c x * (f.residueDegree x : ℤ) := by
  simp [finiteCyclePushforward, AlgebraicCycle.map, AlgebraicCycle.mapCoeff]

/-- A finite pushforward cannot acquire support outside the actual set-theoretic image. -/
theorem finiteCyclePushforward_support_subset (f : X ⟶ Y) [IsFinite f]
    (c : AlgebraicCycle X ℤ) :
    (finiteCyclePushforward f c).support ⊆ f.base '' c.support := by
  change (Function.locallyFinsupp.map f.base (fun x ↦ (f.residueDegree x : ℤ))
    f.isSpectralMap c).support ⊆ f.base '' c.support
  exact Function.locallyFinsupp.support_map_subset_of_forall_mem
    f.isSpectralMap (fun x ↦ (f.residueDegree x : ℤ)) c c.support
    (f.base '' c.support) Set.Subset.rfl (fun x hx _ ↦ ⟨x, hx, rfl⟩)

/-- Finite point support stays finite. This is distinct from finiteness of the
associated integral closed subscheme over a correspondence source. -/
theorem finiteCyclePushforward_finite_support (f : X ⟶ Y) [IsFinite f]
    (c : AlgebraicCycle X ℤ) (hc : c.support.Finite) :
    (finiteCyclePushforward f c).support.Finite :=
  (hc.image f.base).subset (finiteCyclePushforward_support_subset f c)

@[simp]
theorem finiteCyclePushforward_id (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward (𝟙 X) c = c :=
  AlgebraicCycle.map_id (fun _ : X ↦ (0 : ℕ)) c

/-- Composition preserves both residue degrees and the sums over colliding fibres. -/
theorem finiteCyclePushforward_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward g (finiteCyclePushforward f c) =
      finiteCyclePushforward (f ≫ g) c := by
  change Function.locallyFinsupp.map g.base (fun y ↦ (g.residueDegree y : ℤ))
      g.isSpectralMap
      (Function.locallyFinsupp.map f.base (fun x ↦ (f.residueDegree x : ℤ))
        f.isSpectralMap c) =
    Function.locallyFinsupp.map (g.base ∘ f.base)
      (fun x ↦ ((f ≫ g).residueDegree x : ℤ))
      (g.isSpectralMap.comp f.isSpectralMap) c
  apply locallyFinsupp_map_comp_of_weight_mul
  intro x
  rw [residueDegree_comp, Nat.cast_mul, mul_comm]

/-- The finite pushforwards compose as additive homomorphisms. -/
theorem finiteCyclePushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] :
    (finiteCyclePushforward g).comp (finiteCyclePushforward f) =
      finiteCyclePushforward (f ≫ g) := by
  ext c
  exact finiteCyclePushforward_comp_apply f g c

end Stacks.Chow
