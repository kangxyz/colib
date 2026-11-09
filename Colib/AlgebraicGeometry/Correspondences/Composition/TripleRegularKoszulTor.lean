/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRegularImmersion
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleKoszulTor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.PerfectFactor

/-!
# Constructed regular equations compute actual sixfold Tor

The genuine combined inclusion is a regular immersion by the successive-diagonal proof.
The native stalk criterion constructs regular generators of its actual stalk kernel. Those
generators compute every degree of the full exterior-support versus fourfold stalk Tor through
the native coefficient Koszul complex. No regular presentation, Tor comparison, flatness of a
support, finite-length assumption, or Euler equality is supplied by the caller.

This is valid over any base for flat outer structure maps and smooth separated middle maps.
It is consequently compatible with arbitrary fields and disconnected smooth schemes. The
constructed generators are for the combined kernel. The additional comparison with the same
two original middle-diagonal lists, including their signed total complexes, remains separate.
This file does not assert equality with either iterated finite-correspondence bracket.

The construction follows the geometric aim of motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/Aglib/AlgebraicGeometry/Intersection/Triple/CombinedRegularity.lean
(blob 621566dc66d48431f958a13640d8a637c1ef45a5), but uses the native regular-immersion
composition and stalk criterion instead of porting its generic regular-list algebra.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]

omit [IsSeparated h] in
/-- Native regular-immersion geometry constructs the literal combined stalk equations. -/
theorem exists_regular_kernel_correspondenceFourfoldDiagonal
    (q : correspondenceFourfoldProduct f g h i) :
    ∃ (r : ℕ) (a : Fin r → (correspondenceSixfoldAmbient f g h i).presheaf.stalk
      (correspondenceFourfoldDiagonalInclusion f g h i q)),
      RingTheory.Sequence.IsRegular
        ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
          (correspondenceFourfoldDiagonalInclusion f g h i q)) (List.ofFn a) ∧
        RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap q).hom =
          Ideal.span (Set.range a) := by
  obtain ⟨rs, hreg, hspan⟩ :=
    Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
      (correspondenceFourfoldDiagonalInclusion f g h i)
      (isRegularImmersion_correspondenceFourfoldDiagonal f g h i) q
  refine ⟨rs.length, rs.get, ?_, ?_⟩
  · rwa [List.ofFn_get]
  · rw [← hspan, ← Ideal.ofList_ofFn, List.ofFn_get]

/-- Constructed native Koszul homology computes every actual sixfold stalk Tor degree. -/
theorem exists_correspondenceTripleIncidenceTor_iso_koszul
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (v : pullback (C := Scheme) h i)
    (t : correspondenceTripleIncidence f g h i z w v) :
    ∃ (r : ℕ) (a : Fin r → correspondenceTripleIncidenceAmbientStalk f g h i z w v t),
      RingTheory.Sequence.IsRegular
        (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) (List.ofFn a) ∧
      RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom =
          Ideal.span (Set.range a) ∧
      ∀ n : ℕ, Nonempty (correspondenceTripleIncidenceTor f g h i z w v t n ≅
        (Koszul.seqComplexTensor a
          (correspondenceTripleIncidenceSupportStalkModule f g h i z w v t)).homology n) := by
  obtain ⟨r, a, ha, hker⟩ := exists_regular_kernel_correspondenceFourfoldDiagonal f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)
  exact ⟨r, a, ha, hker, fun n =>
    ⟨correspondenceTripleIncidenceTorIsoKoszul f g h i z w v t a ha hker n⟩⟩

end Stacks.Chow
