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
# Finite pushforward of native cycles

This is the additive finite-morphism specialization of Mathlib's actual
`AlgebraicCycle.map`, with constant dimension weights. Its residue-field weights
are unchanged, and all points in each fibre contribute, including collisions and
negative coefficients. No second cycle representation or Chow quotient is used.

The composition proof directly invokes the native Stacks weighted-map Fubini
identity and residue-degree tower formula. The closed-immersion statements use
the native degree-one theorem. These lower cycle statements do not require the
scheme-theoretic-image geometry used by the correspondence application.

## References

* Stacks Project, Tag 02R4: the residue-degree pushforward formula, specialized to
  finite morphisms on ungraded cycles.
* Stacks Project, Tag 02R5: the finite-morphism functoriality formula.
* Stacks Project, Tag 09G9: the multiplicativity of field-extension degrees.
* Mathlib `AlgebraicGeometry/AlgebraicCycle/Basic.lean` and Stacks
  `Chow/ProperPushforwardChow/Functoriality.lean` and
  `Chow/ProperPushforwardPrincipal/ResidueTrdeg.lean` supply the actual maps.

This separates the native cycle algebra from the geometric support argument in
`Correspondences.Composition.Pushforward`, preserving its declaration names.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {X Y Z : Scheme.{u}}

/-- Finite pushforward, on the existing group of native integral-coefficient cycles.
Constant weights do not discard any point: the coefficient is its residue degree. -/
@[stacks 02R4 "residue-degree pushforward formula for finite morphisms on ungraded native cycles"]
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
@[stacks 02R5 "finite-morphism functoriality formula on ungraded native cycles",
  stacks 09G9 "multiplicativity of residue-field degrees is the coefficient input"]
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
  apply AddMonoidHom.ext
  intro c
  exact finiteCyclePushforward_comp_apply f g c


/-! ## Prime coefficients and collisions -/

open Function.locallyFinsuppWithin in
/-- A prime cycle has its actual residue degree after finite pushforward. -/
theorem finiteCyclePushforward_single (r : X ⟶ Y) [IsFinite r] (x : X) (n : ℤ) :
    finiteCyclePushforward r (single x n) =
      single (r.base x) (n * (r.residueDegree x : ℤ)) := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [finiteCyclePushforward_apply, ← finsum_set_coe_eq_finsum_mem]
  by_cases hy : y = r.base x
  · subst y
    rw [finsum_eq_single _ ⟨x, by simp⟩]
    · simp
    · intro z hz
      have hzx : (z : X) ≠ x := fun he ↦ hz (Subtype.ext he)
      simp [single_apply, hzx]
  · have hxy : r.base x ≠ y := Ne.symm hy
    rw [finsum_eq_zero_of_forall_eq_zero]
    · simp [single_apply, hy]
    · intro z
      have hzx : (z : X) ≠ x := fun he ↦ hxy (by simpa [he] using z.2)
      simp [single_apply, hzx]

open Function.locallyFinsuppWithin in
/-- Contributions from colliding source points are added with their separate
residue degrees. No injectivity hypothesis is used or needed. -/
theorem finiteCyclePushforward_single_add_of_image_eq
    (r : X ⟶ Y) [IsFinite r] (x x' : X) (n m : ℤ)
    (himage : r.base x = r.base x') :
    finiteCyclePushforward r (single x n + single x' m) =
      single (r.base x)
        (n * (r.residueDegree x : ℤ) + m * (r.residueDegree x' : ℤ)) := by
  classical
  rw [map_add, finiteCyclePushforward_single, finiteCyclePushforward_single]
  apply Function.locallyFinsuppWithin.ext
  intro y
  by_cases hy : y = r.base x <;> simp [single_apply, ← himage, hy]

/-- A closed immersion preserves the coefficient of each prime cycle. -/
theorem finiteCyclePushforward_single_of_isClosedImmersion (i : X ⟶ Y)
    [IsClosedImmersion i] (x : X) (n : ℤ) :
    finiteCyclePushforward i (Function.locallyFinsuppWithin.single x n) =
      Function.locallyFinsuppWithin.single (i.base x) n := by
  rw [finiteCyclePushforward_single, residueDegree_eq_one_of_isPreimmersion]
  simp

/-- Evaluation after a closed immersion recovers every original coefficient. -/
theorem finiteCyclePushforward_apply_of_isClosedImmersion (i : X ⟶ Y)
    [IsClosedImmersion i] (c : AlgebraicCycle X ℤ) (x : X) :
    finiteCyclePushforward i c (i.base x) = c x := by
  classical
  rw [finiteCyclePushforward_apply, ← finsum_set_coe_eq_finsum_mem]
  rw [finsum_eq_single _ ⟨x, by simp⟩]
  · rw [residueDegree_eq_one_of_isPreimmersion]
    simp
  · intro z hz
    exact (hz (Subtype.ext (i.isClosedEmbedding.injective z.property))).elim

/-- Closed-immersion pushforward is injective on the native group of cycles. -/
theorem finiteCyclePushforward_injective_of_isClosedImmersion (i : X ⟶ Y)
    [IsClosedImmersion i] : Function.Injective (finiteCyclePushforward i) := by
  intro c d h
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hx := congrArg (fun e : AlgebraicCycle Y ℤ => e (i.base x)) h
  simpa only [finiteCyclePushforward_apply_of_isClosedImmersion] using hx

/-- Isomorphism transport and inverse transport cancel on the actual native cycles. -/
@[simp]
theorem finiteCyclePushforward_iso_inv (e : X ≅ Y) (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward e.inv (finiteCyclePushforward e.hom c) = c := by
  simp only [finiteCyclePushforward_comp_apply, e.hom_inv_id, finiteCyclePushforward_id]

/-- Isomorphism transport is an additive equivalence of the native cycle groups. -/
def finiteCyclePushforwardEquiv (e : X ≅ Y) : AlgebraicCycle X ℤ ≃+ AlgebraicCycle Y ℤ where
  toFun := finiteCyclePushforward e.hom
  invFun := finiteCyclePushforward e.inv
  left_inv := finiteCyclePushforward_iso_inv e
  right_inv := finiteCyclePushforward_iso_inv e.symm
  map_add' := (finiteCyclePushforward e.hom).map_add

end Stacks.Chow
