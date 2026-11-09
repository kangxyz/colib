/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleCombinedColumnEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageOriginalPairTor
public import Colib.RingTheory.Koszul.EulerVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The actual original pair first column computes combined-diagonal Tor

The first list is in the middle stalk of the actual original pair incidence.
The proven equality of middle points transports it to the sixfold middle stalk;
the proven equality of stalk maps identifies its pullback with the literal list
used by `correspondenceTripleIncidenceFirstKoszulIsoOriginalPairTor`.
The Z list is in the original sixfold second-middle stalk. Its ideal comparison
is constructed from the original Cartesian diagonal square. All first degrees
are retained in a finsum; bounded Koszul homology proves that this equals the
finite column Euler already compared with combined Tor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence TopologicalSpace
open scoped BigOperators
universe u
namespace Stacks.Chow

private theorem regular_actualMiddle_stalkCongr {V : Scheme.{u}} {a b : V}
    (hab : a = b) (l : List (V.presheaf.stalk a))
    (hl : IsRegular (V.presheaf.stalk a) l) :
    IsRegular (V.presheaf.stalk b)
      (l.map (V.presheaf.stalkCongr (Inseparable.of_eq hab)).hom.hom) := by
  subst b
  simpa [TopCat.Presheaf.stalkCongr] using hl

private theorem seqEuler_map_ofFn_get {R P : Type u} [CommRing R] [CommRing P]
    {r : ℕ} (a : Fin r → R) (φ : R →+* P) (M : ModuleCat P) :
    Koszul.seqEuler (fun j => φ ((List.ofFn a).get j)) M =
      Koszul.seqEuler (fun j => φ (a j)) M :=
  congrArg (fun q : Σ n, Fin n → R => Koszul.seqEuler (fun j => φ (q.2 j)) M)
    (List.equivSigmaTuple.apply_symm_apply ⟨r, a⟩)

section Field
variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)


omit [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] in
/-- The original Z ideal extends to the actual second ambient diagonal ideal. -/
theorem correspondenceActualSecondMiddleFamily_ideal
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let secondMiddleRing := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f
      g h i ambientPoint)
    let secondMiddleMap := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      ambientPoint).hom
    let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      ambientPoint
    ∀ {m : ℕ} (s : Fin m → secondMiddleRing)
    (_hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceSixfoldSecondMiddlePair f g h i ambientPoint) = Ideal.span (Set.range s)),
    secondIdeal = Ideal.ofList (List.ofFn (fun j => secondMiddleMap (s j))) := by
  dsimp only
  intro m s hks
  rw [ker_correspondenceSecondDiagonal, IdealSheafData.stalk_comap, hks,
    Ideal.map_span, ← Set.range_comp]
  exact (Ideal.ofList_ofFn _).symm

/-- The precise original-pair first module family, in every degree, computes the
actual combined-diagonal triple coefficient. The inputs are only regular original
Y and Z families with their original diagonal ideal presentations. -/
theorem finsum_actualPair_remainingFirstEuler_eq_combinedTor
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    let supportPoint := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x.1
    let pairProjection := (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) :
      correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶ correspondenceIncidence f g h z
        w)
    let pairAmbientPoint := correspondenceIncidenceAmbientInclusion f g h z w (pairProjection
      supportPoint)
    let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
    let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
    let pairMiddleRing := (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      pairAmbientPoint)
    let secondMiddleRing := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f
      g h i ambientPoint)
    let pairAmbientMap := correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x.1
    let pairMiddleMap := ((correspondenceMiddlePair f g h).stalkMap pairAmbientPoint).hom
    let secondMiddleMap := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      ambientPoint).hom
    let firstStageMap := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
    ∀ {r m : ℕ} (t : Fin r → pairMiddleRing) (ht : IsRegular pairMiddleRing (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h pairAmbientPoint) = Ideal.span (Set.range t))
    (s : Fin m → secondMiddleRing) (_hs : IsRegular secondMiddleRing (List.ofFn s))
    (_hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceSixfoldSecondMiddlePair f g h i ambientPoint) = Ideal.span (Set.range s)),
    let l := List.ofFn (fun j => pairAmbientMap (pairMiddleMap (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x.1 t ht hkt
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      Koszul.seqEuler (fun j => firstStageMap (secondMiddleMap (s j)))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 l hreg.1 hreg.2 n)) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length ambientRing (correspondenceTripleIncidenceTor f g h i z w v x.1 n)).toNat
          : ℤ) := by
  dsimp only
  intro r m t ht hkt s hs hks
  let supportPoint := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x.1
  let pairProjection := (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) :
    correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶ correspondenceIncidence f g h z w)
  let pairAmbientPoint := correspondenceIncidenceAmbientInclusion f g h z w (pairProjection
    supportPoint)
  let ambientPoint := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
  let ambientRing := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
  let pairMiddleRing := (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
    pairAmbientPoint)
  let firstMiddleRing := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h
    i ambientPoint)
  let pairAmbientMap := correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x.1
  let pairMiddleMap := ((correspondenceMiddlePair f g h).stalkMap pairAmbientPoint).hom
  let firstMiddleMap := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap ambientPoint).hom
  let secondMiddleMap := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap ambientPoint).hom
  let firstStageMap := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
  let firstIdeal := IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
    ambientPoint
  let secondIdeal := IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
    ambientPoint
  classical
  let l := List.ofFn (fun j => pairAmbientMap (pairMiddleMap (t j)))
  let hreg := correspondenceOriginalPairList_first_regular f g h i z w v x.1 t ht hkt
  let e : pairMiddleRing →+* firstMiddleRing := ((pullback g g).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_originalMiddle_point_eq
      f g h i z w v x.1))).hom.hom
  let tY := (List.ofFn t).map e
  have htY : IsRegular firstMiddleRing tY := regular_actualMiddle_stalkCongr
    (correspondenceTripleIncidence_originalMiddle_point_eq f g h i z w v x.1)
    (List.ofFn t) ht
  have hlist : tY.map firstMiddleMap = l := by
    dsimp only [tY, l]
    rw [List.map_map, List.map_ofFn]
    congr 1
    funext j
    simpa only [RingHom.comp_apply, CommRingCat.hom_comp, Function.comp_apply] using
      (congrArg (fun ψ => ψ (t j))
        (correspondenceTripleIncidence_originalMiddle_stalkMap f g h i z w v x.1)).symm
  have hY : firstIdeal = Ideal.ofList (tY.map firstMiddleMap) := by rw [hlist]; exact hreg.2
  have hZ : secondIdeal = Ideal.ofList ((List.ofFn s).map secondMiddleMap) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      correspondenceActualSecondMiddleFamily_ideal k f g h i z w v x s hks
  have hfinite := correspondenceOriginalMiddleLists_remainingEuler_eq_combinedTor
    k f g h i z w v x tY (List.ofFn s) htY hs hY hZ
  let ht' := (correspondenceOriginalMiddleLists_regular_append f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x.1)
    tY (List.ofFn s) htY hs hY hZ).1
  change (∑ n : Fin ((tY.map firstMiddleMap).length + 1), (-1 : ℤ) ^ (n : ℕ) *
    Koszul.seqEuler (fun j => firstStageMap
      (((List.ofFn s).map secondMiddleMap).get j))
      (correspondenceRemainingFirstKoszulModule f g h i z w v x.1
        (tY.map firstMiddleMap) ht' hY n)) = _ at hfinite
  have htransport (L : List ambientRing) (hL : L = l)
      (hr : IsRegular ambientRing L) (hI : firstIdeal = Ideal.ofList L) :
      (∑ n : Fin (L.length + 1), (-1 : ℤ) ^ (n : ℕ) *
        Koszul.seqEuler (fun j => firstStageMap
          (((List.ofFn s).map secondMiddleMap).get j))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 L hr hI n)) =
      ∑ n : Fin (l.length + 1), (-1 : ℤ) ^ (n : ℕ) *
        Koszul.seqEuler (fun j => firstStageMap
          (((List.ofFn s).map secondMiddleMap).get j))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x.1
            l hreg.1 hreg.2 n) := by
    subst L
    rfl
  have hslist : (List.ofFn s).map secondMiddleMap =
      List.ofFn (fun j => secondMiddleMap (s j)) := by
    rw [List.map_ofFn]
    rfl
  have hfinite' :
      (∑ n : Fin (l.length + 1), (-1 : ℤ) ^ (n : ℕ) *
        Koszul.seqEuler (fun j => firstStageMap (secondMiddleMap (s j)))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 l hreg.1 hreg.2 n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length ambientRing (correspondenceTripleIncidenceTor f g h i z w v x.1
            n)).toNat : ℤ) := by
    refine Eq.trans ?_ ((htransport (tY.map firstMiddleMap) hlist ht' hY).symm.trans hfinite)
    apply Finset.sum_congr rfl
    intro n _
    let N := correspondenceRemainingFirstKoszulModule
      f g h i z w v x.1 l hreg.1 hreg.2 n
    have hget := congrArg
      (fun L : List ambientRing => Koszul.seqEuler (fun j => firstStageMap (L.get j)) N)
      hslist
    exact congrArg (fun a : ℤ => (-1 : ℤ) ^ (n : ℕ) * a)
      (hget.trans (seqEuler_map_ofFn_get
        (fun j => secondMiddleMap (s j)) firstStageMap N)).symm
  let H := fun n => correspondenceRemainingFirstKoszulModule
    f g h i z w v x.1 l hreg.1 hreg.2 n
  let F : ℕ → ℤ := fun n => (-1 : ℤ) ^ n * Koszul.seqEuler (fun j => firstStageMap
    (secondMiddleMap (s j))) (H n)
  have hsupport : Function.support F ⊆ (Finset.range (l.length + 1) : Set ℕ) := by
    intro n hn
    apply Finset.mem_range.mpr
    by_contra hbound
    have hlt : l.length < n := by omega
    let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1
    have hkoszul : Koszul.IsKoszulRegular l.get :=
      (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := ambientRing)).2.2
        (by simpa only [List.ofFn_get] using hreg.1)
    have hz := Koszul.isZero_tor_of_lt l.get hkoszul M hlt
    have hH := IsZero.of_iso hz
      (Koszul.torIsoHomologySeqComplexTensor l.get hkoszul M n).symm
    have hsub := ModuleCat.isZero_iff_subsingleton.mp hH
    let : Subsingleton (H n) := hsub
    exact hn (by simp only [F, Koszul.seqEuler_eq_zero_of_subsingleton, mul_zero])
  change (∑ᶠ n, F n) = _
  calc
    (∑ᶠ n, F n) = ∑ n ∈ Finset.range (l.length + 1), F n :=
      finsum_eq_sum_of_support_subset (f := F) hsupport
    _ = ∑ n : Fin (l.length + 1), F n :=
      (Fin.sum_univ_eq_sum_range F (l.length + 1)).symm
    _ = _ := hfinite'

end Field
end Stacks.Chow
