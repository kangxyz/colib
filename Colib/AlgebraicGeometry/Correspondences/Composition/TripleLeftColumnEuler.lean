/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleLeftColumnTor

/-!
# The actual first-stage column Euler sum is the full iterated Tor coefficient

The two actual regular diagonal presentations bound the two Tor indices by their
respective list lengths. The full native finsum therefore equals the finite signed
sum of the remaining Koszul Euler characteristics of the genuine first-stage
homology modules. The scalar ring in those Euler characteristics is the full
first-stage stalk with its proved quotient action. No cutoff, finite-length witness,
module identification, or Euler comparison is supplied by the caller.

At original generic triple points finite lengths are separately proved by
`TripleIteratedTorComparison`; thus ENat.toNat in this specialization discards no
infinite term. This result does not perform global finite-image localization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [IsSeparated g]
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "P" =>
  correspondenceRemainingOriginalStalk f g h i z w v x
local notation3 (prettyPrint := false) "AmbientModule" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "φ" =>
  correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p


omit [IsSeparated g] in
/-- The literal two regular diagonal lists bound both original column indices. -/
theorem isZero_correspondenceTripleIncidenceLeftIteratedTor_of_listLength_lt
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ)
    (hab : s.length < a ∨ t.length < b) :
    IsZero (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b) := by
  let Y := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x
  let Z := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x
  let H := ((Tor (ModuleCat A) b).obj Y).obj AmbientModule
  have hY' : IY = Ideal.span (Set.range t.get) :=
    hY.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])
  have hZ' : IZ = Ideal.span (Set.range s.get) :=
    hZ.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])
  rcases hab with ha | hb
  · let e := ((Tor_iso_Tor' A a).app Z).app H
    apply IsZero.of_iso (Y := ((Tor' (ModuleCat A) a).obj Z).obj H) _ e
    change IsZero (((Tor' (ModuleCat A) a).obj (ModuleCat.of A (A ⧸ IZ))).obj H)
    rw [hZ']
    exact Koszul.isZero_tor_of_lt s.get
      ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
        (M := A) (f := s.get)).2.2
        (by simpa only [List.ofFn_get] using hs)) H ha
  · let : ((Tor (ModuleCat A) a).obj Z).Linear A :=
      leftDerived_linear A ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj Z) a
    let : ((Tor (ModuleCat A) a).obj Z).PreservesZeroMorphisms := by
      constructor
      intro U V
      simpa only [zero_smul] using
        ((Tor (ModuleCat A) a).obj Z).map_smul (0 : A) (0 : U ⟶ V)
    apply ((Tor (ModuleCat A) a).obj Z).map_isZero
    let e := ((Tor_iso_Tor' A b).app Y).app AmbientModule
    apply IsZero.of_iso (Y := ((Tor' (ModuleCat A) b).obj Y).obj AmbientModule) _ e
    change IsZero (((Tor' (ModuleCat A) b).obj (ModuleCat.of A (A ⧸ IY))).obj AmbientModule)
    rw [hY']
    exact Koszul.isZero_tor_of_lt t.get
      ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
        (M := A) (f := t.get)).2.2
        (by simpa only [List.ofFn_get] using ht)) AmbientModule hb

/-- The full signed iterated Tor coefficient equals the literal column Euler sum
over the actual first-stage stalk and its canonical first-homology modules. -/
theorem finsum_signed_leftIteratedTor_eq_sum_remainingFirstEuler
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) :
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length A
        (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x ab.1 ab.2)).toNat : ℤ)) =
      ∑ b : Fin (t.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler (fun j => φ (s.get j))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b) := by
  classical
  let F : ℕ × ℕ → ℤ := fun ab => (-1 : ℤ) ^ (ab.1 + ab.2) *
    ((Module.length A
      (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x ab.1 ab.2)).toNat : ℤ)
  have hrect : Function.support F ⊆
      ((Finset.range (s.length + 1)).product (Finset.range (t.length + 1)) : Set (ℕ × ℕ)) := by
    intro ab hab
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      by_contra ha
      have hz := isZero_correspondenceTripleIncidenceLeftIteratedTor_of_listLength_lt
        f g h i z w v x t s ht hs hY hZ ab.1 ab.2 (Or.inl (lt_of_not_ge ha))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      apply hab
      simp only [F, Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      by_contra hb
      have hz := isZero_correspondenceTripleIncidenceLeftIteratedTor_of_listLength_lt
        f g h i z w v x t s ht hs hY hZ ab.1 ab.2 (Or.inr (lt_of_not_ge hb))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      apply hab
      simp only [F, Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]
  change (∑ᶠ ab : ℕ × ℕ, F ab) = _
  calc
    (∑ᶠ ab : ℕ × ℕ, F ab) =
        ∑ ab ∈ (Finset.range (s.length + 1)).product
            (Finset.range (t.length + 1)), F ab :=
      finsum_eq_sum_of_support_subset (f := F) hrect
    _ = ∑ b ∈ Finset.range (t.length + 1),
        ∑ a ∈ Finset.range (s.length + 1), F (a, b) :=
      Finset.sum_product_right (Finset.range (s.length + 1))
        (Finset.range (t.length + 1)) F
    _ = ∑ b : Fin (t.length + 1),
        ∑ a ∈ Finset.range (s.length + 1), F (a, (b : ℕ)) :=
      (Fin.sum_univ_eq_sum_range
        (fun b : ℕ => ∑ a ∈ Finset.range (s.length + 1), F (a, b))
        (t.length + 1)).symm
    _ = ∑ b : Fin (t.length + 1),
        ∑ a : Fin (s.length + 1), F ((a : ℕ), (b : ℕ)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact (Fin.sum_univ_eq_sum_range (fun a : ℕ => F (a, (b : ℕ)))
        (s.length + 1)).symm
    _ = ∑ b : Fin (t.length + 1), (-1 : ℤ) ^ (b : ℕ) *
            Koszul.seqEuler (fun j => φ (s.get j))
              (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b) := by
      apply Finset.sum_congr rfl
      intro b _
      unfold Koszul.seqEuler
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [F]
      rw [length_correspondenceTripleIncidenceLeftIteratedTor_eq_remainingKoszul
        f g h i z w v x t s ht hs hY hZ (a : ℕ) (b : ℕ), pow_add]
      ring

end Stacks.Chow
