/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRegularKoszulTor
public import StacksFrontier.RingTheory.Koszul.Append

/-!
# Actual sixfold Tor and a genuine successive-diagonal total

The first list generates the actual first-diagonal stalk kernel. The second list consists
of lifts of regular generators of the actual second-diagonal kernel in the first quotient.
Their append is therefore jointly regular, by the native surjective-kernel regular-sequence
lemma. The native signed Koszul append isomorphism identifies actual sixfold Tor with the
homology of the tensor total of these two actual diagonal resolutions, tensored with the
original full exterior-support stalk. No flatness of this coefficient stalk is needed.

Only a list of lifts is chosen. The first quotient, its scalar action, the second kernel,
both complex differentials and their total signs remain the native ones. These lists are
not yet identified with lists pulled from the two original middle-pair stalks in
motivic@a6805c4a87cdfd7717dd7a94039246a167f15380, CommonRegularity.lean
(blob 1514722c4da3fbbb6ab7934f22327894a627bac9). That extra compatibility, finite generic
Euler support, and the original bracket-to-weighted-sum comparison remain separate.

Native suppliers are Stacks 067R/067P/067Q for the actual immersions, the native
`isWeaklyRegular_append_of_ker_eq`, and Stacks 0664 for the signed Koszul total isomorphism.
No generic regular-sequence or tensor-total theorem is redeclared.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- Actual first-kernel generators and lifts from the actual second quotient are jointly regular. -/
theorem exists_correspondenceSuccessiveDiagonalLists [Flat f] [Smooth g] [IsSeparated g]
    [Smooth h] [IsSeparated h] [Flat i] (q : correspondenceFourfoldProduct f g h i) :
    let A := (correspondenceSixfoldAmbient f g h i).presheaf.stalk
      (correspondenceFourfoldDiagonalInclusion f g h i q)
    let B := (correspondenceFirstDiagonal f g h i).presheaf.stalk
      (correspondenceSecondDiagonalInclusion f g h i q)
    let φ := ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
      (correspondenceSecondDiagonalInclusion f g h i q)).hom
    let ψ := ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom
    ∃ t s : List A,
      RingTheory.Sequence.IsRegular A t ∧
      Ideal.ofList t = RingHom.ker φ ∧
      RingTheory.Sequence.IsRegular B (s.map φ) ∧
      Ideal.ofList (s.map φ) = RingHom.ker ψ ∧
      RingTheory.Sequence.IsRegular A (t ++ s) ∧
      Ideal.ofList (t ++ s) =
        RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap q).hom := by
  dsimp only
  let A := (correspondenceSixfoldAmbient f g h i).presheaf.stalk
    (correspondenceFourfoldDiagonalInclusion f g h i q)
  let φ := ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
    (correspondenceSecondDiagonalInclusion f g h i q)).hom
  let ψ := ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom
  obtain ⟨t, ht, hkt⟩ :=
    Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
      (correspondenceFirstDiagonalInclusion f g h i)
      (isRegularImmersion_correspondenceFirstDiagonal f g h i)
      (correspondenceSecondDiagonalInclusion f g h i q)
  obtain ⟨s₀, hs₀, hks₀⟩ :=
    Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
      (correspondenceSecondDiagonalInclusion f g h i)
      (isRegularImmersion_correspondenceSecondDiagonal f g h i) q
  have hφ : Function.Surjective φ := SurjectiveOnStalks.stalkMap_surjective
    (correspondenceFirstDiagonalInclusion f g h i)
    (correspondenceSecondDiagonalInclusion f g h i q)
  obtain ⟨s, hs⟩ := List.map_surjective_iff.mpr hφ s₀
  have hker : Ideal.ofList (t ++ s) = RingHom.ker (ψ.comp φ) := by
    rw [Ideal.ofList_append, hkt, ← RingHom.comap_ker ψ φ, ← hks₀, ← hs,
      ← Ideal.map_ofList, Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot]
    exact sup_comm _ _
  have hregular : RingTheory.Sequence.IsRegular A (t ++ s) := by
    refine ⟨Stacks.AlgebraicGeometry.isWeaklyRegular_append_of_ker_eq φ hφ
      ht.toIsWeaklyRegular hkt.symm (hs ▸ hs₀.toIsWeaklyRegular), ?_⟩
    rw [show Ideal.ofList (t ++ s) • (⊤ : Submodule A A) = Ideal.ofList (t ++ s) by
      rw [Ideal.smul_eq_mul, Ideal.mul_top], hker]
    exact (RingHom.ker_ne_top (ψ.comp φ)).symm
  refine ⟨t, s, ht, hkt, hs ▸ hs₀, hs ▸ hks₀, hregular, ?_⟩
  dsimp only [correspondenceFourfoldDiagonalInclusion]
  rw [Scheme.Hom.stalkMap_comp]
  exact hker

variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The native signed total of two diagonal complexes with the actual exterior coefficients. -/
abbrev correspondenceTripleIncidenceTwoListTotal
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)) :=
  (((tensoringRight (ModuleCat
    (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))).obj
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
          (Koszul.totTensor (Koszul.seqComplex t.get) (Koszul.seqComplex s.get))

/-- Actual combined-diagonal Tor is the homology of the native signed two-list total. -/
def correspondenceTripleIncidenceTorIsoTwoListTotal [IsSeparated g] [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) (t ++ s))
    (hker : Ideal.ofList (t ++ s) =
      RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)).hom) (n : ℕ) :
    correspondenceTripleIncidenceTor f g h i z w v x n ≅
      (correspondenceTripleIncidenceTwoListTotal f g h i z w v x t s).homology n := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
  let a := Fin.append t.get s.get
  have ha : RingTheory.Sequence.IsRegular A (List.ofFn a) := by
    simpa only [a, List.ofFn_fin_append, List.ofFn_get] using hr
  have hk : RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)).hom =
        Ideal.span (Set.range a) := by
    rw [← Ideal.ofList_ofFn, a, List.ofFn_fin_append, List.ofFn_get, List.ofFn_get]
    exact hker.symm
  let T := ((tensoringRight (ModuleCat A)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)
  let e := (Koszul.tensoringRightSeqComplexIso a M).symm ≪≫
    T.mapIso (Koszul.seqComplexAppendIsoTotTensor t.get s.get)
  exact correspondenceTripleIncidenceTorIsoKoszul f g h i z w v x a ha hk n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).mapIso e

/-- Smooth original middle factors construct a genuine two-stage total computing all Tor degrees. -/
theorem exists_correspondenceTripleIncidenceTor_iso_twoListTotal
    [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]
    (x : correspondenceTripleIncidence f g h i z w v) :
    ∃ t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x),
      Ideal.ofList t = RingHom.ker
        ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
          (correspondenceSecondDiagonalInclusion f g h i
            (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x))).hom ∧
      Ideal.ofList (s.map ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
        (correspondenceSecondDiagonalInclusion f g h i
          (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x))).hom) =
        RingHom.ker ((correspondenceSecondDiagonalInclusion f g h i).stalkMap
          (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)).hom ∧
      ∀ n : ℕ, Nonempty (correspondenceTripleIncidenceTor f g h i z w v x n ≅
        (correspondenceTripleIncidenceTwoListTotal f g h i z w v x t s).homology n) := by
  obtain ⟨t, s, _, hkt, _, hks, hr, hker⟩ :=
    exists_correspondenceSuccessiveDiagonalLists f g h i
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)
  exact ⟨t, s, hkt, hks, fun n =>
    ⟨correspondenceTripleIncidenceTorIsoTwoListTotal f g h i z w v x t s hr hker n⟩⟩

end Stacks.Chow
