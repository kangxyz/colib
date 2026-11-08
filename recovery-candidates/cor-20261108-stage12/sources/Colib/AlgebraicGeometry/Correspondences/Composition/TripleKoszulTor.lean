/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleStalkModules
public import StacksFrontier.RingTheory.Koszul.TorComparison.QuotientTor
public import Mathlib.RingTheory.Length

/-!
# Actual sixfold Tor computed by the native coefficient Koszul complex

The second Tor input is the full fourfold stalk with its original combined-diagonal scalar
action. Its quotient comparison is induced by that actual stalk map, and sends each ambient
germ to its image. Native Tor functoriality, symmetry (Stacks 00M3), and the native quotient
Koszul comparison identify every actual Tor degree with native `Koszul.seqComplexTensor`
homology. There is no caller-provided Tor or homology comparison.

The regular presentation is an explicit input here. `TripleRegularKoszulTor` constructs one
from smoothness of both original middle factors. This module does not assert that this native
Koszul model already equals the two original separate middle-list totals or either Cor bracket.
It supplies the exact module and degreewise comparison those further identifications need.

The mathematical step corresponds to motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Correspondences/Composition/Associativity/IncidenceTor.lean (blob
4c2fa80bcc39e51a964cc7a25d3b1daa17ddda96). The complex and Tor comparison here are entirely
native Stacks, using its finite-indexed exterior-power Koszul model rather than porting the
original recursive list-complex implementation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual combined-diagonal stalk quotient, with the literal ambient scalar action. -/
def correspondenceTripleIncidenceDiagonalStalkQuotientIso [IsSeparated g] [IsSeparated h]
    (t : correspondenceTripleIncidence f g h i z w v) :
    ModuleCat.of (correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v t ⧸
        RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
          (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom) ≅
      correspondenceTripleIncidenceFourfoldStalkModule f g h i z w v t := by
  let φ := ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom
  have hφ : Function.Surjective φ := SurjectiveOnStalks.stalkMap_surjective
    (correspondenceFourfoldDiagonalInclusion f g h i)
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)
  let e := φ.quotientKerEquivOfSurjective hφ
  letI : Module (correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
      ((correspondenceFourfoldProduct f g h i).presheaf.stalk
        (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)) := Module.compHom _ φ
  apply LinearEquiv.toModuleIso
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a b
  change e (a • b) = φ a * e b
  rw [Algebra.smul_def, map_mul]
  exact congrArg (· * e b) (RingHom.quotientKerEquivOfSurjective_apply_mk hφ a)

/-- On every ambient germ, the module comparison is the original combined-diagonal stalk map. -/
@[simp]
theorem correspondenceTripleIncidenceDiagonalStalkQuotientIso_mk
    [IsSeparated g] [IsSeparated h]
    (t : correspondenceTripleIncidence f g h i z w v)
    (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :
    (correspondenceTripleIncidenceDiagonalStalkQuotientIso f g h i z w v t).hom
      (Ideal.Quotient.mk _ a) =
        ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
          (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom a := by
  rfl

/-- Every genuine regular presentation computes every degree of actual sixfold stalk Tor. -/
def correspondenceTripleIncidenceTorIsoKoszul [IsSeparated g] [IsSeparated h]
    (t : correspondenceTripleIncidence f g h i z w v) {r : ℕ}
    (a : Fin r → correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
    (ha : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) (List.ofFn a))
    (hker : RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom =
        Ideal.span (Set.range a)) (n : ℕ) :
    correspondenceTripleIncidenceTor f g h i z w v t n ≅
      (Koszul.seqComplexTensor a
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v t)).homology n := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v t
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v t
  let J := RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom
  let Q := ModuleCat.of A (A ⧸ J)
  exact ((Tor (ModuleCat A) n).obj M).mapIso
      (correspondenceTripleIncidenceDiagonalStalkQuotientIso f g h i z w v t).symm ≪≫
    (((Tor_iso_Tor' A n) ≪≫ (torFlip_iso_Tor' A n).symm).app M).app Q ≪≫
    Koszul.torIsoHomologySeqComplexTensorOfIsRegular a ha J hker M n

/-- The degreewise comparison preserves full ambient module lengths, including infinite length. -/
theorem correspondenceTripleIncidenceTor_length_eq_koszul [IsSeparated g] [IsSeparated h]
    (t : correspondenceTripleIncidence f g h i z w v) {r : ℕ}
    (a : Fin r → correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
    (ha : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) (List.ofFn a))
    (hker : RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom =
        Ideal.span (Set.range a)) (n : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
      (correspondenceTripleIncidenceTor f g h i z w v t n) =
        Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
          ((Koszul.seqComplexTensor a
            (correspondenceTripleIncidenceSupportStalkModule f g h i z w v t)).homology n) :=
  (correspondenceTripleIncidenceTorIsoKoszul f g h i z w v t a ha hker n).toLinearEquiv.length_eq

end Stacks.Chow
