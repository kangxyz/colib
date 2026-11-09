/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleSuccessiveKoszulTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleStalkIdeal
public import StacksFrontier.AlgebraicGeometry.Flatness.StalkIdealSheaf
public import Mathlib.RingTheory.Regular.Flat

/-!
# The original middle-diagonal lists in the actual common ambient

The lists are chosen in the original Y and Z self-product stalks. They are pulled into the
actual sixfold stalk by the two original middle-pair projections. The same second list is
then regular in the actual first-diagonal quotient, by the flat remaining-middle map. Their
literal images, not new chosen lifts, give the jointly regular append used by the native
signed total comparison.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380, TripleIdeals.lean
(blob 83346c82c61d0b6b039f608f618f7fce4c11c3bc) and CommonRegularity.lean
(blob 1514722c4da3fbbb6ab7934f22327894a627bac9). Native replacements are the regular-immersion
stalk criterion, `Stacks.Flatness.ker_stalkMap_of_isPullback`, and Mathlib's faithfully-flat
regular-sequence base change. The private point-transport calculation only removes the
native stalkCongr from an ideal stalk; it does not reprove the base-change theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

private theorem map_idealStalk_stalkCongr {X : Scheme.{u}} (I : X.IdealSheafData)
    {x y : X} (h : x = y) :
    (IdealSheafData.stalk I x).map
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom = IdealSheafData.stalk I y := by
  subst h
  simp [TopCat.Presheaf.stalkCongr]

private theorem ker_stalkMap_eq_map_idealStalk_of_isPullback
    {X X' S S' : Scheme.{u}} {iX : X ⟶ X'} {gX : X ⟶ S}
    {gX' : X' ⟶ S'} {iS : S ⟶ S'}  [IsClosedImmersion iS]
    (H : IsPullback iX gX gX' iS) (x : X) :
    RingHom.ker (iX.stalkMap x).hom =
      (IdealSheafData.stalk iS.ker (gX' (iX x))).map (gX'.stalkMap (iX x)).hom := by
  have hp : iS (gX x) = gX' (iX x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m x) H.w.symm
  have hk := Stacks.Flatness.ker_stalkMap_of_isPullback H x hp
  rw [ker_stalkMap_eq_idealStalk_ker iS (gX x), CommRingCat.hom_comp,
    ← Ideal.map_map, map_idealStalk_stalkCongr _ hp] at hk
  exact hk

private theorem exists_regular_diagonalIdeal_stalk {S Y : Scheme.{u}}
    (g : Y ⟶ S) [Smooth g] [IsSeparated g] (y : Y) (p : pullback (C := Scheme) g g)
    (hp : pullback.diagonal g y = p) :
    ∃ rs : List ((pullback g g).presheaf.stalk p),
      IsRegular ((pullback g g).presheaf.stalk p) rs ∧
        IdealSheafData.stalk (pullback.diagonal g).ker p = Ideal.ofList rs := by
  subst p
  obtain ⟨rs, hrs, hker⟩ :=
    Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
      (pullback.diagonal g)
      (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
        (pullback.fst g g) (pullback.diagonal g) (pullback.diagonal_fst g)) y
  exact ⟨rs, hrs, (ker_stalkMap_eq_idealStalk_ker (pullback.diagonal g) y).symm.trans hker.symm⟩

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- Original self-product stalk lists generate both actual diagonal ideals after pullback. -/
theorem exists_correspondenceOriginalMiddleLists [Smooth g] [IsSeparated g]
    [Smooth h] [IsSeparated h] (q : correspondenceFourfoldProduct f g h i) :
    let p := correspondenceFourfoldDiagonalInclusion f g h i q
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t ∧
      IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s ∧
      IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) ∧
      IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) := by
  dsimp only
  let y := correspondenceSecondDiagonalInclusion f g h i q
  let z := correspondenceFourfoldToSecondAmbient f g h i q
  have hy := congrArg (fun m => m y) (correspondenceSixfoldFirstDiagonal_isPullback f g h i).w
  have hz := congrArg (fun m => m z) (correspondenceSixfoldSecondDiagonal_isPullback f g h i).w
  have he := congrArg (fun m => m q) (correspondenceFourfold_diagonals_comm f g h i)
  change correspondenceFirstDiagonalInclusion f g h i y =
    correspondenceSecondAmbientInclusion f g h i z at he
  change pullback.diagonal h
      ((pullback.fst (correspondenceAmbientTarget f g h) (pullback.fst h i) ≫
        correspondenceAmbientTarget f g h) z) =
    correspondenceSixfoldSecondMiddlePair f g h i
      (correspondenceSecondAmbientInclusion f g h i z) at hz
  rw [← he] at hz
  change pullback.diagonal g
      ((pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
        correspondenceTripleMiddle f g h) y) =
    correspondenceSixfoldFirstMiddlePair f g h i
      (correspondenceFourfoldDiagonalInclusion f g h i q) at hy
  obtain ⟨t, ht, hyt⟩ := exists_regular_diagonalIdeal_stalk g _ _ hy
  obtain ⟨s, hs, hzs⟩ := exists_regular_diagonalIdeal_stalk h _ _ hz
  refine ⟨t, s, ht, hs, ?_, ?_⟩
  · have hk := ker_stalkMap_eq_map_idealStalk_of_isPullback
      (correspondenceSixfoldFirstDiagonal_isPullback f g h i).flip y
    rw [ker_stalkMap_eq_idealStalk_ker] at hk
    change IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceFourfoldDiagonalInclusion f g h i q) =
        (IdealSheafData.stalk (pullback.diagonal g).ker
          (correspondenceSixfoldFirstMiddlePair f g h i
            (correspondenceFourfoldDiagonalInclusion f g h i q))).map
          ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
            (correspondenceFourfoldDiagonalInclusion f g h i q)).hom at hk
    rw [hyt, Ideal.map_ofList] at hk
    exact hk
  · have hk := ker_stalkMap_eq_map_idealStalk_of_isPullback
      (correspondenceSixfoldSecondDiagonal_isPullback f g h i).flip z
    rw [ker_stalkMap_eq_idealStalk_ker, ← he, hzs, Ideal.map_ofList] at hk
    exact hk

/-- The same original second list is regular in the first quotient, so the literal append
is regular and generates the actual combined kernel. -/
theorem correspondenceOriginalMiddleLists_regular_append
    [Flat f] [Flat g] [Flat h] [Flat i] [IsSeparated g] [IsSeparated h]
    (q : correspondenceFourfoldProduct f g h i) :
    let p := correspondenceFourfoldDiagonalInclusion f g h i q
    ∀ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t →
      IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s →
      IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom) →
      IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) →
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p) t' ∧
      IsRegular ((correspondenceFirstDiagonal f g h i).presheaf.stalk
        (correspondenceSecondDiagonalInclusion f g h i q))
        (s'.map ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (correspondenceSecondDiagonalInclusion f g h i q)).hom) ∧
      RingHom.ker ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom =
        Ideal.ofList (s'.map ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (correspondenceSecondDiagonalInclusion f g h i q)).hom) ∧
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p) (t' ++ s') ∧
      RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap q).hom =
        Ideal.ofList (t' ++ s') := by
  dsimp only
  intro t s ht hs hkt hks
  let q₁ := correspondenceSecondDiagonalInclusion f g h i q
  let p := correspondenceFourfoldDiagonalInclusion f g h i q
  let A := (correspondenceSixfoldAmbient f g h i).presheaf.stalk p
  let B := (correspondenceFirstDiagonal f g h i).presheaf.stalk q₁
  let R₁ := (pullback g g).presheaf.stalk (correspondenceSixfoldFirstMiddlePair f g h i p)
  let R₂ := (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
  let a : R₁ →+* A := ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
  let b : R₂ →+* A := ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
  let φ : A →+* B := ((correspondenceFirstDiagonalInclusion f g h i).stalkMap q₁).hom
  let t' : List A := t.map a
  let s' : List A := s.map b
  have hfirst : IsRegular A t' := by
    let : Algebra R₁ A := a.toAlgebra
    have : Module.Flat R₁ A := Flat.stalkMap (correspondenceSixfoldFirstMiddlePair f g h i) p
    have : IsLocalHom (algebraMap R₁ A) := by
      change IsLocalHom ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      infer_instance
    have : Module.FaithfullyFlat R₁ A := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact ht.of_faithfullyFlat
  have hsecond : IsRegular B (s'.map φ) := by
    have : Flat (correspondenceFirstDiagonalInclusion f g h i ≫
        correspondenceSixfoldSecondMiddlePair f g h i) := by
      rw [correspondenceFirstDiagonal_secondMiddlePair]
      infer_instance
    have hflat : (φ.comp b).Flat := by
      have hf := Flat.stalkMap (correspondenceFirstDiagonalInclusion f g h i ≫
        correspondenceSixfoldSecondMiddlePair f g h i) q₁
      rw [Scheme.Hom.stalkMap_comp] at hf
      exact hf
    let : Algebra R₂ B := (φ.comp b).toAlgebra
    have : Module.Flat R₂ B := hflat
    have : IsLocalHom (algebraMap R₂ B) := by
      change IsLocalHom (φ.comp b)
      dsimp only [φ, b]
      infer_instance
    have : Module.FaithfullyFlat R₂ B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hr : IsRegular B (s.map (φ.comp b)) := hs.of_faithfullyFlat
    simpa only [s', List.map_map, RingHom.coe_comp] using hr
  have hkfirst : RingHom.ker φ = Ideal.ofList t' :=
    (ker_stalkMap_eq_idealStalk_ker (correspondenceFirstDiagonalInclusion f g h i) q₁).trans hkt
  have hksecond : RingHom.ker ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom =
      Ideal.ofList (s'.map φ) := by
    have hk := ker_stalkMap_eq_map_idealStalk_of_isPullback
      (correspondenceFourfold_diagonals_isPullback f g h i) q
    change RingHom.ker ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom =
      (IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p).map φ at hk
    rw [hks, Ideal.map_ofList] at hk
    exact hk
  have hker : Ideal.ofList (t' ++ s') =
      RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap q).hom := by
    rw [ker_stalkMap_eq_idealStalk_ker]
    change Ideal.ofList (t' ++ s') = IdealSheafData.stalk
      (correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).ker p
    rw [ker_correspondenceFourfoldDiagonal, IdealSheafData.stalk_sup, hkt, hks,
      Ideal.ofList_append]
  have happend : IsRegular A (t' ++ s') := by
    refine ⟨Stacks.AlgebraicGeometry.isWeaklyRegular_append_of_ker_eq φ
      (SurjectiveOnStalks.stalkMap_surjective (correspondenceFirstDiagonalInclusion f g h i) q₁)
      hfirst.toIsWeaklyRegular hkfirst hsecond.toIsWeaklyRegular, ?_⟩
    rw [show Ideal.ofList (t' ++ s') • (⊤ : Submodule A A) = Ideal.ofList (t' ++ s') by
      rw [Ideal.smul_eq_mul, Ideal.mul_top], hker]
    exact (RingHom.ker_ne_top _).symm
  exact ⟨hfirst, hsecond, hksecond, happend, hker.symm⟩

/-- The original middle-pair lists pulled by the actual maps compute every sixfold Tor degree. -/
theorem exists_correspondenceOriginalMiddleLists_tor_iso
    [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (v : pullback (C := Scheme) h i)
    (x : correspondenceTripleIncidence f g h i z w v) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
      let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
      IsRegular ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)) t ∧
      IsRegular ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p)) s ∧
      IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p =
        Ideal.ofList t' ∧
      IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList s' ∧
      ∀ n : ℕ, Nonempty (correspondenceTripleIncidenceTor f g h i z w v x n ≅
        (correspondenceTripleIncidenceTwoListTotal f g h i z w v x t' s').homology n) := by
  dsimp only
  let q := correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x
  obtain ⟨t, s, ht, hs, hkt, hks⟩ := exists_correspondenceOriginalMiddleLists f g h i q
  obtain ⟨_, _, _, hr, hker⟩ :=
    correspondenceOriginalMiddleLists_regular_append f g h i q t s ht hs hkt hks
  exact ⟨t, s, ht, hs, hkt, hks, fun n =>
    ⟨correspondenceTripleIncidenceTorIsoTwoListTotal f g h i z w v x _ _ hr hker.symm n⟩⟩

end Stacks.Chow

