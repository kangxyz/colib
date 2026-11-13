/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PointControl
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pairing

/-!
# Signed support provenance for native correspondence composition

Decompose both native input cycles using their own finite supports and original
integer coefficients. If every prime-pair output coefficient vanishes, the actual
signed biadditive composition coefficient vanishes. Thus a surviving output has
an actual contributing pair. Combining this with finite-image closedness lifts
every point of the surviving integral support to that pair's incidence scheme.

Implementation source: `kangxyz/motivic` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/PointControl.lean`,
blob `a406042039c0a29d86e865a2ec06b2214e3b4d66`.
The source's custom generator/Finsupp presentation is not retained.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable [Smooth g] [Smooth h] [IsSeparated h]

/-- A nonzero coefficient of the signed pairing comes from a pair of actual
input support points. Cancellation can remove contributions but cannot create one. -/
theorem exists_pair_of_incidenceTorPairing_ne_zero
    (α : finiteCorrespondences f g) (β : finiteCorrespondences g h)
    (b : pullback (C := Scheme) f h)
    (hb : (incidenceTorPairing f g h α β).val b ≠ 0) :
    ∃ z : α.property.1.toFinset, ∃ w : β.property.1.toFinset,
      ∃ hz : IsFiniteCorrespondencePoint f g z.val,
      ∃ hw : IsFiniteCorrespondencePoint g h w.val,
        (incidenceTorCorrespondence f g h z.val w.val hz hw).val b ≠ 0 := by
  classical
  let I := ↥α.property.1.toFinset
  let J := ↥β.property.1.toFinset
  have hz (z : I) : IsFiniteCorrespondencePoint f g z.val :=
    α.property.2 z.val (by
      simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using z.property)
  have hw (w : J) : IsFiniteCorrespondencePoint g h w.val :=
    β.property.2 w.val (by
      simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using w.property)
  let a (z : I) := singleFiniteCorrespondence f g z.val (hz z) (α.val z.val)
  let d (w : J) := singleFiniteCorrespondence g h w.val (hw w) (β.val w.val)
  have hα : α = ∑ z : I, a z := finiteCorrespondence_eq_sum_signedSingles f g α
  have hβ : β = ∑ w : J, d w := finiteCorrespondence_eq_sum_signedSingles g h β
  let ev : finiteCorrespondences f h →+ ℤ :=
    { toFun := fun γ => γ.val b
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  by_contra hn
  have hp (z : I) (w : J) :
      (incidenceTorCorrespondence f g h z.val w.val (hz z) (hw w)).val b = 0 := by
    by_contra hp
    exact hn ⟨z, w, hz z, hw w, hp⟩
  apply hb
  change ev (incidenceTorPairing f g h α β) = 0
  rw [hα, map_sum]
  simp only [AddMonoidHom.finsetSum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro z _
  rw [hβ, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro w _
  rw [incidenceTorPairing_single, map_zsmul]
  change (α.val z.val * β.val w.val) •
    (incidenceTorCorrespondence f g h z.val w.val (hz z) (hw w)).val b = 0
  rw [hp, smul_zero]

/-- Every actual point of every surviving output component of an arbitrary
signed native composition comes from the actual incidence of input supports. -/
theorem exists_incidence_point_of_incidenceTorPairing_ne_zero
    (α : finiteCorrespondences f g) (β : finiteCorrespondences g h)
    (b : pullback (C := Scheme) f h)
    (hb : (incidenceTorPairing f g h α β).val b ≠ 0)
    (c : (integralComponentAt b).subscheme) :
    ∃ z : α.property.1.toFinset, ∃ w : β.property.1.toFinset,
      ∃ a : correspondenceIncidence f g h z.val w.val,
        correspondenceIncidenceMap f g h z.val w.val a =
          (integralComponentAt b).subschemeι c := by
  obtain ⟨z, w, hz, hw, hp⟩ := exists_pair_of_incidenceTorPairing_ne_zero f g h α β b hb
  obtain ⟨a, ha⟩ := exists_incidence_point_of_incidenceTorCorrespondence_ne_zero
    f g h z.val w.val hz hw b hp c
  exact ⟨z, w, a, ha⟩

end Stacks.Chow
