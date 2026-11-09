/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleIteratedTorComparison

/-!
# The actual Z-first column in the unchanged sixfold local ring

Native quotient Tor identifies the right iterated Tor module with Y-Koszul
homology of Z-Koszul homology, on the already defined full exterior coefficient
module. Both lists generate the literal diagonal stalk ideals. Their native
regular resolutions bound the two indices and identify the full signed finsum
with the finite column Euler sum, with no caller cutoff or comparison equality.

This lower owner does not import the pending right exterior geometry or construct
an action on an abstract Tor module. Its scalar ring is the original sixfold stalk.
The separate right-column consumer attaches the existing actual quotient action.
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
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "AmbientModule" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

/-- Right iterated Tor is actual remaining Y-homology of actual first Z-homology. -/
def correspondenceTripleIncidenceRightIteratedTorIsoAmbientKoszul
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b ≅
      (Koszul.seqComplexTensor t.get
        ((Koszul.seqComplexTensor s.get AmbientModule).homology b)).homology a := by
  let H := (Koszul.seqComplexTensor s.get AmbientModule).homology b
  let eZ := Koszul.torIsoHomologySeqComplexTensorOfIsRegular s.get
    (by simpa only [List.ofFn_get] using hs) IZ
    (hZ.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])) AmbientModule b
  let eY := Koszul.torIsoHomologySeqComplexTensorOfIsRegular t.get
    (by simpa only [List.ofFn_get] using ht) IY
    (hY.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])) H a
  exact ((Tor (ModuleCat A) a).obj
    (correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x)).mapIso eZ ≪≫ eY

/-- The actual ambient comparison preserves every raw length. -/
theorem length_correspondenceTripleIncidenceRightIteratedTor_eq_ambientKoszul
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    Module.length A (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b) =
      Module.length A
        ((Koszul.seqComplexTensor t.get
          ((Koszul.seqComplexTensor s.get AmbientModule).homology b)).homology a) :=
  (correspondenceTripleIncidenceRightIteratedTorIsoAmbientKoszul
    f g h i z w v x t s ht hs hY hZ a b).toLinearEquiv.length_eq

/-- The two original regular presentations bound both right column indices. -/
theorem isZero_correspondenceTripleIncidenceRightIteratedTor_of_listLength_lt
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ)
    (hab : t.length < a ∨ s.length < b) :
    IsZero (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b) := by
  let Y := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x
  let Z := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x
  let H := ((Tor (ModuleCat A) b).obj Z).obj AmbientModule
  have hY' : IY = Ideal.span (Set.range t.get) :=
    hY.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])
  have hZ' : IZ = Ideal.span (Set.range s.get) :=
    hZ.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])
  rcases hab with ha | hb
  · let e := ((Tor_iso_Tor' A a).app Y).app H
    apply IsZero.of_iso (Y := ((Tor' (ModuleCat A) a).obj Y).obj H) _ e
    change IsZero (((Tor' (ModuleCat A) a).obj (ModuleCat.of A (A ⧸ IY))).obj H)
    rw [hY']
    exact Koszul.isZero_tor_of_lt t.get
      ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
        (M := A) (f := t.get)).2.2
        (by simpa only [List.ofFn_get] using ht)) H ha
  · let : ((Tor (ModuleCat A) a).obj Y).Linear A :=
      leftDerived_linear A ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj Y) a
    let : ((Tor (ModuleCat A) a).obj Y).PreservesZeroMorphisms := by
      constructor
      intro U V
      simpa only [zero_smul] using
        ((Tor (ModuleCat A) a).obj Y).map_smul (0 : A) (0 : U ⟶ V)
    apply ((Tor (ModuleCat A) a).obj Y).map_isZero
    let e := ((Tor_iso_Tor' A b).app Z).app AmbientModule
    apply IsZero.of_iso (Y := ((Tor' (ModuleCat A) b).obj Z).obj AmbientModule) _ e
    change IsZero (((Tor' (ModuleCat A) b).obj (ModuleCat.of A (A ⧸ IZ))).obj AmbientModule)
    rw [hZ']
    exact Koszul.isZero_tor_of_lt s.get
      ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
        (M := A) (f := s.get)).2.2
        (by simpa only [List.ofFn_get] using hs)) AmbientModule hb

/-- The full right iterated coefficient is its literal ambient column Euler sum. -/
theorem finsum_signed_rightIteratedTor_eq_sum_ambientFirstEuler
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) :
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length A
        (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x ab.1 ab.2)).toNat : ℤ)) =
      ∑ b : Fin (s.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler t.get ((Koszul.seqComplexTensor s.get AmbientModule).homology b) := by
  classical
  let F : ℕ × ℕ → ℤ := fun ab => (-1 : ℤ) ^ (ab.1 + ab.2) *
    ((Module.length A
      (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x ab.1 ab.2)).toNat : ℤ)
  have hrect : Function.support F ⊆
      ((Finset.range (t.length + 1)).product (Finset.range (s.length + 1)) : Set (ℕ × ℕ)) := by
    intro ab hab
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      by_contra ha
      have hz := isZero_correspondenceTripleIncidenceRightIteratedTor_of_listLength_lt
        f g h i z w v x t s ht hs hY hZ ab.1 ab.2 (Or.inl (lt_of_not_ge ha))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      apply hab
      simp only [F, Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]
    · apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      by_contra hb
      have hz := isZero_correspondenceTripleIncidenceRightIteratedTor_of_listLength_lt
        f g h i z w v x t s ht hs hY hZ ab.1 ab.2 (Or.inr (lt_of_not_ge hb))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      apply hab
      simp only [F, Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]
  change (∑ᶠ ab : ℕ × ℕ, F ab) = _
  calc
    (∑ᶠ ab : ℕ × ℕ, F ab) =
        ∑ ab ∈ (Finset.range (t.length + 1)).product
            (Finset.range (s.length + 1)), F ab :=
      finsum_eq_sum_of_support_subset (f := F) hrect
    _ = ∑ b ∈ Finset.range (s.length + 1),
        ∑ a ∈ Finset.range (t.length + 1), F (a, b) :=
      Finset.sum_product_right (Finset.range (t.length + 1))
        (Finset.range (s.length + 1)) F
    _ = ∑ b : Fin (s.length + 1),
        ∑ a ∈ Finset.range (t.length + 1), F (a, (b : ℕ)) :=
      (Fin.sum_univ_eq_sum_range
        (fun b : ℕ => ∑ a ∈ Finset.range (t.length + 1), F (a, b))
        (s.length + 1)).symm
    _ = ∑ b : Fin (s.length + 1),
        ∑ a : Fin (t.length + 1), F ((a : ℕ), (b : ℕ)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact (Fin.sum_univ_eq_sum_range (fun a : ℕ => F (a, (b : ℕ)))
        (t.length + 1)).symm
    _ = ∑ b : Fin (s.length + 1), (-1 : ℤ) ^ (b : ℕ) *
            Koszul.seqEuler t.get
              ((Koszul.seqComplexTensor s.get AmbientModule).homology b) := by
      apply Finset.sum_congr rfl
      intro b _
      unfold Koszul.seqEuler
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [F]
      rw [length_correspondenceTripleIncidenceRightIteratedTor_eq_ambientKoszul
        f g h i z w v x t s ht hs hY hZ (a : ℕ) (b : ℕ), pow_add]
      ring

end Stacks.Chow
