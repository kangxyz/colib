/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleOriginalColumnEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleKoszulTor
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Remaining-first Euler and combined-diagonal Tor

The public native triple-Tor theorem is applied to (Z quotient, Y quotient,
full exterior stalk). The two diagonal quotients are Tor independent because
the original concatenated diagonal list is regular. Thus its right-hand side
has only its inner degree-zero row, which is the actual combined diagonal.
No spectral-sequence equality or support bound is supplied by the caller.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingTheory.Sequence TopologicalSpace
open scoped BigOperators TensorProduct
universe u

namespace CategoryTheory

/-- The native degree-zero Tor of two quotient rings is the quotient by their sum. -/
def torZeroQuotientQuotientIso (A : Type u) [CommRing A] (I J : Ideal A) :
    (((Tor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
      (ModuleCat.of A (A ⧸ J))) ≅ ModuleCat.of A (A ⧸ I ⊔ J) := by
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ I) J).symm
  let e' := DoubleQuot.quotQuotEquivQuotSupₐ A I J
  exact (Functor.leftDerivedZeroIsoSelf (tensorLeft (ModuleCat.of A (A ⧸ I)))).app
      (ModuleCat.of A (A ⧸ J)) ≪≫
    (e.toLinearEquiv.restrictScalars A).toModuleIso ≪≫ e'.toLinearEquiv.toModuleIso

end CategoryTheory

namespace Koszul

/-- Appending regular equations makes the two original equation quotients Tor independent. -/
theorem isZero_tor_quotients_of_regular_append (A : Type u) [CommRing A]
    (t s : List A) (hs : IsRegular A s) (hts : IsRegular A (t ++ s))
    (I J : Ideal A) (hI : I = Ideal.ofList t) (hJ : J = Ideal.ofList s)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (((Tor (ModuleCat A) n).obj (ModuleCat.of A (A ⧸ J))).obj
      (ModuleCat.of A (A ⧸ I))) := by
  have hw := ((RingTheory.Sequence.isWeaklyRegular_append_iff A t s).mp
    hts.toIsWeaklyRegular).2
  have hweak : IsWeaklyRegular (A ⧸ I) s := by
    subst I
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hw
  let e := Koszul.torIsoHomologySeqComplexTensorOfIsRegular s.get
    (by simpa only [List.ofFn_get] using hs) J
    (hJ.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])) (A ⧸ I) n
  exact IsZero.of_iso
    ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1
      (by simpa only [List.ofFn_get] using hweak)) n hn) e

end Koszul

/-- Finsums supported on the zero row collapse without any finite-support premise. -/
theorem finsum_natPair_eq_zeroRow (F : ℕ × ℕ → ℤ)
    (hF : ∀ a b, b ≠ 0 → F (a, b) = 0) :
    (∑ᶠ ab, F ab) = ∑ᶠ a, F (a, 0) := by
  classical
  let j : ℕ → ℕ × ℕ := fun a => (a, 0)
  have hj : Function.Injective j := fun a b hab => congrArg Prod.fst hab
  calc
    _ = ∑ᶠ ab, if h : ab ∈ Set.range j then F (j (Classical.choose h)) else 0 := by
      apply finsum_congr
      intro ab
      split_ifs with h
      · rw [Classical.choose_spec h]
      · exact hF ab.1 ab.2 (fun hb => h ⟨ab.1, Prod.ext rfl hb.symm⟩)
    _ = _ := finsum_emb_domain' hj (fun a => F (j a))

namespace Stacks.Chow

section Actual
variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [IsSeparated g] [IsSeparated h]


/-- Reassociate by first taking Tor of the two genuine diagonal quotients. -/
abbrev correspondenceTripleIncidenceDiagonalFirstTor
    (x : correspondenceTripleIncidence f g h i z w v) :
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
    ∀ (a b : ℕ),
    ModuleCat ambientRing := by
  dsimp only
  intro a b
  let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let firstQuotient := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x
  let secondQuotient := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x
  let exteriorModule := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
  exact ((Tor (ModuleCat ambientRing) a).obj (((Tor (ModuleCat ambientRing) b).obj
    secondQuotient).obj firstQuotient)).obj exteriorModule

/-- Its inner degree-zero term is the original combined-diagonal Tor, not a new coefficient. -/
def correspondenceTripleIncidenceDiagonalFirstZeroIso
    (x : correspondenceTripleIncidence f g h i z w v) :
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      ambientPoint
    let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      ambientPoint
    let combinedKernel := RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)).hom
    ∀ (t s : List ambientRing) (hY : firstIdeal = Ideal.ofList t) (hZ : secondIdeal = Ideal.ofList
      s)
    (hK : combinedKernel = Ideal.ofList (t ++ s)) (a : ℕ),
    correspondenceTripleIncidenceDiagonalFirstTor f g h i z w v x a 0 ≅
      correspondenceTripleIncidenceTor f g h i z w v x a := by
  dsimp only
  intro t s hY hZ hK a
  let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let exteriorModule := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
  let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
  let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
    ambientPoint
  let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
    ambientPoint
  let combinedKernel := RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)).hom
  have heq : secondIdeal ⊔ firstIdeal = combinedKernel := by rw [hY, hZ, hK, Ideal.ofList_append,
    sup_comm]
  let eQ : ModuleCat.of ambientRing (ambientRing ⧸ secondIdeal ⊔ firstIdeal) ≅ ModuleCat.of
    ambientRing (ambientRing ⧸ combinedKernel) :=
    eqToIso (congrArg (fun J : Ideal ambientRing => ModuleCat.of ambientRing (ambientRing ⧸ J)) heq)
  let e := torZeroQuotientQuotientIso ambientRing secondIdeal firstIdeal ≪≫ eQ ≪≫
    correspondenceTripleIncidenceDiagonalStalkQuotientIso f g h i z w v x
  exact (((Tor (ModuleCat ambientRing) a).mapIso e).app exteriorModule) ≪≫
    (((Tor_iso_Tor' ambientRing a) ≪≫ (torFlip_iso_Tor' ambientRing a).symm).app
      (correspondenceTripleIncidenceFourfoldStalkModule f g h i z w v x)).app exteriorModule

/-- All positive inner rows vanish on the actual original diagonal quotients. -/
theorem isZero_correspondenceTripleIncidenceDiagonalFirstTor
    (x : correspondenceTripleIncidence f g h i z w v) :
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      ambientPoint
    let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      ambientPoint
    ∀ (t s : List ambientRing) (hs : IsRegular ambientRing s) (hts : IsRegular ambientRing (t ++ s))
    (hY : firstIdeal = Ideal.ofList t) (hZ : secondIdeal = Ideal.ofList s)
    (a b : ℕ) (hb : b ≠ 0),
    IsZero (correspondenceTripleIncidenceDiagonalFirstTor f g h i z w v x a b) := by
  dsimp only
  intro t s hs hts hY hZ a b hb
  let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let firstQuotient := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x
  let secondQuotient := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x
  let exteriorModule := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
  let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
  let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
    ambientPoint
  let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
    ambientPoint
  let H := ((Tor (ModuleCat ambientRing) b).obj secondQuotient).obj firstQuotient
  let e := (((Tor_iso_Tor' ambientRing a) ≪≫ (torFlip_iso_Tor' ambientRing a).symm).app H).app
    exteriorModule
  exact IsZero.of_iso (((Tor (ModuleCat ambientRing) a).obj exteriorModule).map_isZero
    (Koszul.isZero_tor_quotients_of_regular_append ambientRing t s hs hts firstIdeal secondIdeal
      hY hZ b hb)) e

/-- Collapse the original reassociated double Euler to the actual combined coefficient. -/
theorem finsum_diagonalFirstTor_eq_combinedTor
    (x : correspondenceTripleIncidence f g h i z w v) :
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      ambientPoint
    let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      ambientPoint
    let combinedKernel := RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)).hom
    ∀ (t s : List ambientRing) (hs : IsRegular ambientRing s) (hts : IsRegular ambientRing (t ++ s))
    (hY : firstIdeal = Ideal.ofList t) (hZ : secondIdeal = Ideal.ofList s)
    (hK : combinedKernel = Ideal.ofList (t ++ s)),
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length ambientRing (correspondenceTripleIncidenceDiagonalFirstTor
        f g h i z w v x ab.1 ab.2)).toNat : ℤ)) =
      ∑ᶠ a : ℕ, (-1 : ℤ) ^ a *
        ((Module.length ambientRing (correspondenceTripleIncidenceTor f g h i z w v x a)).toNat :
          ℤ) := by
  dsimp only
  intro t s hs hts hY hZ hK
  rw [finsum_natPair_eq_zeroRow _ (fun a b hb => by
    have hz := isZero_correspondenceTripleIncidenceDiagonalFirstTor
      f g h i z w v x t s hs hts hY hZ a b hb
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero])]
  apply finsum_congr
  intro a
  rw [(correspondenceTripleIncidenceDiagonalFirstZeroIso
    f g h i z w v x t s hY hZ hK a).toLinearEquiv.length_eq, Nat.add_zero]
end Actual

section Field
variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)


/-- Native triple Tor, reordered so that the two diagonal quotients are paired together.
All regularity, finite-module, support and dimension hypotheses are constructed here. -/
theorem finsum_leftIteratedTor_eq_diagonalFirstTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length ambientRing (correspondenceTripleIncidenceLeftIteratedTor
        f g h i z w v x.1 ab.1 ab.2)).toNat : ℤ)) =
    ∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length ambientRing (correspondenceTripleIncidenceDiagonalFirstTor
        f g h i z w v x.1 ab.1 ab.2)).toNat : ℤ) := by
  dsimp only
  let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
  let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
  let Y := correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x.1
  let Z := correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x.1
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1
  have : IsRegularLocalRing ambientRing := isRegularLocalRing_correspondenceSixfoldAmbient_stalk
    k f g h i ambientPoint
  have : IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceSixfoldAmbientToField k f g h i)
  have : Module.Finite ambientRing M := finite_correspondenceTripleIncidenceSupportStalkModule
    f g h i z w v x.1
  exact Stacks.Intersection.finsum_alternating_length_tor_assoc_of_isRegularLocalRing
    ambientRing Z Y M (correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x.1)
    (ringKrullDim_eq_correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x.1).le
    (fun q hq => support_correspondenceTripleIncidence_threeModules f g h i z w v x
      ⟨⟨hq.1.2, hq.2⟩, hq.1.1⟩)

/-- The signed remaining-first Koszul Euler is the actual combined-diagonal Tor coefficient. -/
theorem sum_remainingFirstEuler_eq_combinedTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let firstStageMap := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
    let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      ambientPoint
    let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      ambientPoint
    let combinedKernel := RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1)).hom
    ∀ (t s : List ambientRing) (ht : IsRegular ambientRing t) (hs : IsRegular ambientRing s)
    (hts : IsRegular ambientRing (t ++ s))
    (hY : firstIdeal = Ideal.ofList t) (hZ : secondIdeal = Ideal.ofList s)
    (hK : combinedKernel = Ideal.ofList (t ++ s)),
    (∑ b : Fin (t.length + 1), (-1 : ℤ) ^ (b : ℕ) *
      Koszul.seqEuler (fun j => firstStageMap (s.get j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t ht hY b)) =
      ∑ᶠ a : ℕ, (-1 : ℤ) ^ a *
        ((Module.length ambientRing (correspondenceTripleIncidenceTor f g h i z w v x.1 a)).toNat
          : ℤ) := by
  dsimp only
  intro t s ht hs hts hY hZ hK
  exact (finsum_signed_leftIteratedTor_eq_sum_remainingFirstEuler
    f g h i z w v x.1 t s ht hs hY hZ).symm.trans
    ((finsum_leftIteratedTor_eq_diagonalFirstTor k f g h i z w v x).trans
      (finsum_diagonalFirstTor_eq_combinedTor f g h i z w v x.1 t s hs hts hY hZ hK))


/-- Original middle lists give the combined coefficient with every regularity and
kernel comparison supplied by their actual geometric construction. -/
theorem correspondenceOriginalMiddleLists_remainingEuler_eq_combinedTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let firstStageMap := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
    let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      ambientPoint
    let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      ambientPoint
    let firstMiddleRing := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g
      h i ambientPoint)
    let secondMiddleRing := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f
      g h i ambientPoint)
    let firstMiddleMap := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap ambientPoint).hom
    let secondMiddleMap := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      ambientPoint).hom
    ∀ (t : List firstMiddleRing) (s : List secondMiddleRing) (ht : IsRegular firstMiddleRing t)
      (hs : IsRegular secondMiddleRing s)
    (hY : firstIdeal = Ideal.ofList (t.map firstMiddleMap)) (hZ : secondIdeal = Ideal.ofList
      (s.map secondMiddleMap)),
    let t' := t.map firstMiddleMap
    let s' := s.map secondMiddleMap
    let ht' := (correspondenceOriginalMiddleLists_regular_append f g h i
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1) t s ht hs hY hZ).1
    (∑ b : Fin (t'.length + 1), (-1 : ℤ) ^ (b : ℕ) *
      Koszul.seqEuler (fun j => firstStageMap (s'.get j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t' ht' hY b)) =
      ∑ᶠ a : ℕ, (-1 : ℤ) ^ a *
        ((Module.length ambientRing (correspondenceTripleIncidenceTor f g h i z w v x.1 a)).toNat
          : ℤ) := by
  dsimp only
  intro t s ht hs hY hZ
  dsimp only
  have hr := correspondenceOriginalMiddleLists_regular_append f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1) t s ht hs hY hZ
  exact sum_remainingFirstEuler_eq_combinedTor k f g h i z w v x _ _ hr.1
    (correspondenceCommonSecondList_rightFirst_regular f g h i z w v x.1 s hs hZ).1
    hr.2.2.2.1 hY hZ hr.2.2.2.2

/-- Smoothness chooses the original lists; no replacement equations or comparison
witnesses are required to obtain the actual combined-diagonal coefficient. -/
theorem exists_correspondenceOriginalMiddleLists_remainingEuler_eq_combinedTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let firstStageMap := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
    let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      ambientPoint
    let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      ambientPoint
    let firstMiddleRing := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g
      h i ambientPoint)
    let secondMiddleRing := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f
      g h i ambientPoint)
    let firstMiddleMap := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap ambientPoint).hom
    let secondMiddleMap := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      ambientPoint).hom
    ∃ (t : List firstMiddleRing) (s : List secondMiddleRing) (ht : IsRegular firstMiddleRing t)
      (hs : IsRegular secondMiddleRing s)
      (hY : firstIdeal = Ideal.ofList (t.map firstMiddleMap)) (hZ : secondIdeal = Ideal.ofList
        (s.map secondMiddleMap)),
      let t' := t.map firstMiddleMap
      let s' := s.map secondMiddleMap
      let ht' := (correspondenceOriginalMiddleLists_regular_append f g h i
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1) t s ht hs hY hZ).1
      (∑ b : Fin (t'.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler (fun j => firstStageMap (s'.get j))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t' ht' hY b)) =
        ∑ᶠ a : ℕ, (-1 : ℤ) ^ a *
          ((Module.length ambientRing (correspondenceTripleIncidenceTor f g h i z w v x.1
            a)).toNat : ℤ) := by
  dsimp only
  obtain ⟨t, s, ht, hs, hY, hZ⟩ := exists_correspondenceOriginalMiddleLists f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1)
  exact ⟨t, s, ht, hs, hY, hZ,
    correspondenceOriginalMiddleLists_remainingEuler_eq_combinedTor
      k f g h i z w v x t s ht hs hY hZ⟩

end Field
end Stacks.Chow
