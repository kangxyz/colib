/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.CenterControl

/-!
# Signed algebra of actual target-fiber control

The predicate here quantifies over every point of every nonzero native support
component over the specified source point. It introduces no correspondence or
cycle model. Addition, integer multiplication, finite sums and actual Tor
composition preserve the displayed target constraints. Cancellation is allowed.

These are the native signed-support arguments used by the source
`Motivic/Transfers/Sheaf/Germs/Pointed/Lifts/CorrespondenceAlgebra.lean`,
blob `d809712c6c984af6081bd2e5456c5d095f630c50`, at motivic revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u v

namespace Stacks.Chow.finiteCorrespondences

section Basic

variable {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}

/-- Actual target points above one source point, quantified on all surviving
integral support schemes of the original native cycle. -/
def TargetsIn (α : finiteCorrespondences f g) (x : X) (S : Set Y) : Prop :=
  ∀ a : pullback (C := Scheme) f g, α.val a ≠ 0 →
    ∀ t : (integralComponentAt a).subscheme,
      ((integralComponentAt a).subschemeι ≫ pullback.fst f g) t = x →
      ((integralComponentAt a).subschemeι ≫ pullback.snd f g) t ∈ S

namespace TargetsIn

variable {α β : finiteCorrespondences f g} {x : X} {S : Set Y}

/-- The zero native cycle has no support points to control. -/
theorem zero : TargetsIn (0 : finiteCorrespondences f g) x S := by
  intro a ha
  exact (ha rfl).elim

/-- A surviving point in an addition comes from at least one input support. -/
theorem add (hα : TargetsIn α x S) (hβ : TargetsIn β x S) :
    TargetsIn (α + β) x S := by
  intro a ha t ht
  by_cases h : α.val a = 0
  · have hb : β.val a ≠ 0 := by
      change α.val a + β.val a ≠ 0 at ha
      simpa only [h, zero_add] using ha
    exact hβ a hb t ht
  · exact hα a h t ht

/-- Integer scalar multiplication may cancel support but cannot create it. -/
theorem zsmul (hα : TargetsIn α x S) (n : ℤ) : TargetsIn (n • α) x S := by
  intro a ha t ht
  have h : α.val a ≠ 0 := by
    intro hz
    apply ha
    change n • α.val a = 0
    rw [hz, smul_zero]
  exact hα a h t ht

/-- Negation retains all actual support points, with their reversed coefficients. -/
theorem neg (hα : TargetsIn α x S) : TargetsIn (-α) x S := by
  simpa only [neg_one_zsmul] using hα.zsmul (-1)

/-- Finite sums preserve actual target control, including an empty sum. -/
theorem sum {I : Type v} (s : Finset I) (a : I → finiteCorrespondences f g)
    (ha : ∀ i ∈ s, TargetsIn (a i) x S) : TargetsIn (∑ i ∈ s, a i) x S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (zero (f := f) (g := g) (x := x) (S := S))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (ha i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

/-- Enlarge the designated target set without changing the native cycle. -/
theorem mono {T : Set Y} (hα : TargetsIn α x S) (hST : S ⊆ T) : TargetsIn α x T :=
  fun a ha t ht => hST (hα a ha t ht)

end TargetsIn

end Basic

section Composition

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth g] [Smooth h] [IsSeparated h]

/-- Actual signed composition transports designated target sets through all
intermediate support points, using the native incidence-point theorem. -/
theorem TargetsIn.comp
    {α : finiteCorrespondences f g} {β : finiteCorrespondences g h}
    {x : X} {S : Set Y} {T : Set Z}
    (hα : TargetsIn α x S) (hβ : ∀ y ∈ S, TargetsIn β y T) :
    TargetsIn (incidenceTorPairing f g h α β) x T := by
  intro b hb t ht
  apply target_mem_of_incidenceTorPairing_ne_zero f g h α β x S T ?_ ?_ b hb t ht
  · intro a d hd
    apply hα a.val ?_ d hd
    simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using a.property
  · intro a d hd
    apply hβ (((integralComponentAt a.val).subschemeι ≫ pullback.fst g h) d) hd
      a.val ?_ d rfl
    simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using a.property

end Composition

end Stacks.Chow.finiteCorrespondences
