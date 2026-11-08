/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteModel
public import Colib.RingTheory.Koszul.GenericFiniteReindex
public import Colib.RingTheory.Koszul.FinitePushforwardRegular

/-!
# Generic Euler devissage on the actual full finite model

The image local ring is the stalk at an actual generic remaining-image
intersection. Its remaining ideal of definition is proved by the full scheme's
generic Artinian stalk, not supplied as a colength hypothesis. The finite algebra
is the ring of the entire original exterior above that stalk.

For finite modules over this actual algebra, remaining Koszul homology is finite
when the original ambient list is regular. Signed Euler is expanded over every
original minimal prime with its true residue degree. No finite-map flatness or
minimal-contraction hypothesis is imposed.

The module family is explicit. This file does not claim that an arbitrary
family is the first Tor family: its realization over the whole finite model and
the matching of local generic weights with original first-stage Tor coefficients
are separate, necessary interfaces.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated h]
  [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation "R" => correspondenceRemainingImageStalk f g h i z w v x.1
local notation "B" => correspondenceRemainingFiniteRing f g h i z w v x.1
local notation "A" => (pullback h h).presheaf.stalk
  (correspondenceLeftImageMiddlePair f g h i z w v
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))
local notation "α" => correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1

/-- Finite length of each actual remaining homology module over the whole finite
algebra follows from the original regular diagonal and the actual generic point. -/
theorem length_correspondenceRemainingFiniteKoszul_ne_top {r : ℕ} (s : Fin r → A)
    (hr : RingTheory.Sequence.IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s))
    (M : ModuleCat.{u} B) [Module.Finite B M] (n : ℕ) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    Module.length B
      ((Koszul.seqComplexTensor (fun j => algebraMap R B (α (s j))) M).homology n) ≠ ⊤ := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
  let := α.toAlgebra
  exact Koszul.length_seqComplexTensor_finiteAlgebra_ne_top_of_isRegular s hr M
    (isIdealOfDefinition_correspondenceRemainingImageMiddleList f g h i z w v x s hs) n

/-- Signed integer Euler on the full original finite algebra, with every
minimal source prime and original residue degree. The finite-colength input is
proved by the actual generic remaining-image intersection. -/
theorem sum_signed_seqEuler_correspondenceRemainingFiniteModel {r : ℕ} (s : Fin r → A)
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s))
    (M : ℕ → ModuleCat.{u} B) [∀ b, Module.Finite B (M b)] (J : Finset ℕ) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ b ∈ J, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : {q : PrimeSpectrum B // IsMin q},
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          ((Module.length (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat : ℤ)) *
              (Stacks.Length.primeResidueDegree (algebraMap R B)
                (q.1.asIdeal.comap (algebraMap R B)) q.1.asIdeal : ℤ) *
                  Koszul.seqEuler (fun j => α (s j))
                    (R ⧸ q.1.asIdeal.comap (algebraMap R B)) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
  exact Koszul.sum_signed_seqEuler_restrictScalars_eq_finsum_minimalSourcePrimes
    (fun j => α (s j)) M
    (isIdealOfDefinition_correspondenceRemainingImageMiddleList f g h i z w v x s hs) J

end Stacks.Chow
