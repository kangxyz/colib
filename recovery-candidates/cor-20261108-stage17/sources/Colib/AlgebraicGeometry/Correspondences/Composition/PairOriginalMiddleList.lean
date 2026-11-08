/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.PerfectFactor

/-!
# A regular family at the actual original pair middle point

A point of the full original pair incidence maps into the original Y diagonal. Native
smooth-section regularity (Stacks 067R) and the native regular-stalk-kernel supplier choose
a regular generating family in that exact original Y self-product stalk. The actual
Cartesian square identifies the point; no separate search for a regular family is required.

The same ordered family then computes every degree of the original pair Tor as support-ring
Koszul homology, using the previously proved canonical incidence action and support-linear
comparison. This does not assume geometric integrality, connectedness, or a perfect field.
The native providers are `isRegularImmersion_of_smooth_section` and
`RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion`; their proofs are reused.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (x : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "p" => correspondenceIncidenceAmbientInclusion f g h z w x
local notation3 (prettyPrint := false) "m" => correspondenceMiddlePair f g h p
local notation3 (prettyPrint := false) "R" => (pullback g g).presheaf.stalk m
local notation3 (prettyPrint := false) "D" =>
  (correspondenceSupportProduct f g h z w).presheaf.stalk
    (correspondenceIncidenceToSupportProduct f g h z w x)
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair f g h).stalkMap p).hom
local notation3 (prettyPrint := false) "ρ" => correspondenceIncidenceSupportStalkMap f g h z w x

/-- Native smooth-diagonal regularity supplies a family at the exact original pair middle point. -/
theorem exists_correspondenceIncidenceOriginalMiddleList [Smooth g] [IsSeparated g] :
    ∃ (r : ℕ) (t : Fin r → R), IsRegular R (List.ofFn t) ∧
      IdealSheafData.stalk (pullback.diagonal g).ker m = Ideal.span (Set.range t) := by
  let q := correspondenceIncidenceInclusion f g h z w x
  let y := correspondenceTripleMiddle f g h q
  have hp : pullback.diagonal g y = m := by
    simpa only [y, q, correspondenceTripleMiddle, Scheme.Hom.comp_apply] using
      congrArg (fun a => a q) (correspondenceTriple_isPullback f g h).w
  have hex : ∃ l : List ((pullback g g).presheaf.stalk (pullback.diagonal g y)),
      IsRegular ((pullback g g).presheaf.stalk (pullback.diagonal g y)) l ∧
        IdealSheafData.stalk (pullback.diagonal g).ker (pullback.diagonal g y) =
          Ideal.ofList l := by
    obtain ⟨l, hl, hk⟩ :=
      Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
        (pullback.diagonal g)
        (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
          (pullback.fst g g) (pullback.diagonal g) (pullback.diagonal_fst g)) y
    exact ⟨l, hl, (ker_stalkMap_eq_idealStalk_ker (pullback.diagonal g) y).symm.trans hk.symm⟩
  rw [hp] at hex
  obtain ⟨l, hl, hk⟩ := hex
  refine ⟨l.length, l.get, ?_, ?_⟩
  · simpa only [List.ofFn_get] using hl
  · rw [← Ideal.ofList_ofFn, List.ofFn_get]
    exact hk

/-- One native family at the original middle point computes all original pair Tor degrees. -/
theorem exists_correspondenceIncidenceOriginalMiddleList_tor
    [Flat f] [Smooth g] [IsSeparated g] [Flat h] :
    ∃ (r : ℕ) (t : Fin r → R), IsRegular R (List.ofFn t) ∧
      IdealSheafData.stalk (pullback.diagonal g).ker m = Ideal.span (Set.range t) ∧
      ∀ n : ℕ,
        letI := correspondenceIncidenceTorSupportModule f g h z w x n
        Nonempty (correspondenceIncidenceAmbientTor f g h z w x n ≃ₗ[D]
          ((Koszul.seqComplexTensor (fun j => ρ (β (t j))) D).homology n)) := by
  obtain ⟨r, t, ht, hkt⟩ := exists_correspondenceIncidenceOriginalMiddleList f g h z w x
  refine ⟨r, t, ht, hkt, ?_⟩
  intro n
  exact ⟨correspondenceIncidenceTorOriginalSupportLinearEquiv f g h z w x t ht hkt n⟩

end Stacks.Chow
