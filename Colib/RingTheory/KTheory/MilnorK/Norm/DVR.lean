/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.CompletionBranch
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTensorBaseChange
public import Colib.RingTheory.AdicCompletion.FractionBranches

/-!
# Chosen norm and residue over every actual original DVR branch

The base DVR is not assumed complete. A finite torsion-free Dedekind model
supplies all original branches. The proof uses the actual completed tensor
product and its native fraction coordinates, then descends the complete norm
square through the inverse actual completion residue map. The conclusion keeps
the specified original fraction field and each original localized DVR.

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/DVR.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 30–98. The original residue
characteristic-zero hypothesis and all branches are retained. No norm square,
branch enumeration, uniformizer or completeness witness is an input.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing _root_.AdicCompletion
open scoped TensorProduct

universe u

variable (R S F E : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
  [Module.IsTorsionFree R S] [DecidableEq (Ideal S)]
  [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [FiniteDimensional F E]

local notation "J" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "CR" => AdicCompletion (maximalIdeal R) R
local notation "QR" => FractionRing CR
local notation "C" => fun q : IdealBranch J => FractionRing (BranchCompletion J q)
local notation "eR" => RingEquiv.ofBijective
  (ResidueField.map (algebraMap R CR)) (AdicCompletion.residueField_map_bijective R)

/-- The actual finite chosen norm commutes with the sum of residues at every original branch. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_eq_sum_originalBranches
    (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    letI := fun q : IdealBranch J => originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch J => originalBranchIsFractionRing S E q
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      ∑ q : IdealBranch J,
        milnorKNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n
          (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E n x) := by
  let := fun q : IdealBranch J => originalBranchFractionAlgebra S E q
  let := fun q : IdealBranch J => originalBranchIsFractionRing S E q
  let := fun q : IdealBranch J => originalBranchFractionTower S E q
  let := fractionCompletionAlgebra R F
  let := fractionCompletionIsScalarTower R F
  let := fun q : IdealBranch J => localCompletionBaseAlgebra (maximalIdeal R) q
  let := fun q : IdealBranch J => localCompletionBaseFinite (maximalIdeal R)
    (map_maximalIdeal_ne_zero R S) q
  let := fun q : IdealBranch J => localCompletionBaseIsScalarTower (maximalIdeal R) q
  let := fun q : IdealBranch J => localCompletionBase_isLocalHom R S q
  let := fun q : IdealBranch J => localCompletionFractionAlgebra R S q
  let := fun q : IdealBranch J => localCompletionFractionIsScalarTower R S q
  let := fun q : IdealBranch J => localCompletionFractionFinite R S q
  have : CharZero (ResidueField CR) := (eR).symm.toRingHom.charZero
  have : CharZero CR := (IsLocalRing.residue CR).charZero
  have : CharZero QR := charZero_of_injective_algebraMap (IsFractionRing.injective CR QR)
  let ε : (QR ⊗[F] E) ≃ₐ[QR] (∀ q : IdealBranch J, C q) :=
    fractionTensorEquivLocalFractionFields R S F E
  have hscalar : IsFractionRing.lift (A := R) (K := F)
      (g := algebraMap R QR) (dvrCompletionFraction_algebraMap_injective R) =
        algebraMap F QR :=
    dvrCompletionFractionLift_unique R F (algebraMap F QR)
      (fractionCompletionAlgebra_algebraMap_apply R F)
  have hcompletion : milnorKTransport (eR).symm.toRingHom n
      (dvrMilnorTameSymbol' CR QR n
        (milnorKTransport (algebraMap F QR) (n + 1)
          (milnorKNorm F E (n + 1) x))) =
      dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) := by
    simpa only [hscalar, milnorKTheoryMap_eq_transport,
      AddMonoidHom.coe_toIntLinearMap] using
      dvrMilnorTameSymbol'_completion_identification R F n (milnorKNorm F E (n + 1) x)
  have hbase : milnorKTransport (algebraMap F QR) (n + 1)
      (milnorKNorm F E (n + 1) x) =
      ∑ q : IdealBranch J, milnorKNorm QR (C q) (n + 1)
        (milnorKTransport ((Pi.evalRingHom C q).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) (n + 1) x) :=
    milnorKNorm_map_eq_sum_tensorProductPiEquiv ε (n + 1) x
  let A : MilnorKTheory QR (n + 1) →+ MilnorKTheory (ResidueField R) n :=
    (milnorKTransport (eR).symm.toRingHom n).comp (dvrMilnorTameSymbol' CR QR n)
  refine hcompletion.symm.trans ((congrArg A hbase).trans ?_)
  refine (map_sum A
    (fun q : IdealBranch J => milnorKNorm QR (C q) (n + 1)
      (milnorKTransport ((Pi.evalRingHom C q).comp
        (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) (n + 1) x))
    Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro q _
  let φ : E →+* C q := IsFractionRing.lift (A := Localization.AtPrime q.val) (K := E)
    (g := algebraMap (Localization.AtPrime q.val) (C q))
    (dvrCompletionFraction_algebraMap_injective (Localization.AtPrime q.val))
  have hcoordinate : (Pi.evalRingHom C q).comp
      (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) = φ :=
    fractionTensorEquivLocalFractionFields_coordinate R S F E q
  have hmap : milnorKTheoryMap φ (n + 1) x = milnorKTransport φ (n + 1) x :=
    DFunLike.congr_fun (milnorKTheoryMap_eq_transport (n := n + 1) φ) x
  have hcoordinateValue := congrArg
    (fun f : E →+* C q => A (milnorKNorm QR (C q) (n + 1)
      (milnorKTransport f (n + 1) x))) hcoordinate
  refine hcoordinateValue.trans ?_
  refine (congrArg
    (fun y : MilnorKTheory (C q) (n + 1) => A (milnorKNorm QR (C q) (n + 1) y))
    hmap.symm).trans ?_
  exact dvrMilnorTameSymbol_completed_norm_eq_original_branch
    R (Localization.AtPrime q.val) E n x

/-- The full original-branch norm-residue square as an equality of native additive maps. -/
theorem dvrMilnorTameSymbol'_comp_milnorKNorm_eq_sum_originalBranches (n : ℕ) :
    letI := fun q : IdealBranch J => originalBranchFractionAlgebra S E q
    letI := fun q : IdealBranch J => originalBranchIsFractionRing S E q
    (dvrMilnorTameSymbol' R F n).comp (milnorKNorm F E (n + 1)) =
      ∑ q : IdealBranch J,
        (milnorKNorm (ResidueField R) (ResidueField (Localization.AtPrime q.val)) n).comp
          (dvrMilnorTameSymbol' (Localization.AtPrime q.val) E n) := by
  let := fun q : IdealBranch J => originalBranchFractionAlgebra S E q
  let := fun q : IdealBranch J => originalBranchIsFractionRing S E q
  apply AddMonoidHom.ext
  intro x
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.finsetSum_apply] using
    dvrMilnorTameSymbol'_milnorKNorm_eq_sum_originalBranches R S F E n x

end Stacks.Chow

end

attribute [colib_tag "COL-1002",
  colib_ref "aglib_milnor_4f65be4e"
    "KTheory/MilnorK/Norm/FiniteExtension/DVR.lean:39-98" "adaptation"
    "The norm–residue identity summed over the original DVR branches"]
  Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_eq_sum_originalBranches
  Stacks.Chow.dvrMilnorTameSymbol'_comp_milnorKNorm_eq_sum_originalBranches
