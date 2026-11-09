/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRightAmbientColumn
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstStageAction
public import Colib.RingTheory.Koszul.RestrictionComparison
public import StacksFrontier.RingTheory.Koszul.Localization

/-!
# The actual right exterior action on the remaining Y-Koszul column

The existing Z-first quotient construction supplies the action of the literal
full right-exterior stalk on Z-Koszul homology of the unchanged common support.
Its scalar equation identifies the restricted module with the original ambient
module. Native coefficient functoriality and the arbitrary-ring-map Koszul
projection formula identify the whole remaining column with its actual
right-exterior realization. The true stalk map is surjective, so lengths agree.

This consumer imports only `RightFirstStageAction`, not the subsequent pair-base-
change, original-pair Tor or Tor-sheaf leaves. It creates no alternative geometry,
no action on abstract Tor, and no transpose of a finite correspondence. Both
ordered lists, all homological degrees and the full scheme structures are retained.
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
  [IsSeparated h]
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x)
local notation3 (prettyPrint := false) "AmbientModule" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

/-- The unchanged Z-first homology with its existing actual right-exterior stalk action. -/
abbrev correspondenceRightRemainingFirstKoszulModule
    (s : List A) (hs : IsRegular A s) (hZ : IZ = Ideal.ofList s) (b : ℕ) : ModuleCat P :=
  letI := correspondenceTripleIncidenceRightFirstKoszulModule f g h i z w v x s hs hZ b
  ModuleCat.of P ((Koszul.seqComplexTensor s.get AmbientModule).homology b)

/-- Restriction of the genuine right-exterior action is the original ambient action. -/
def correspondenceTripleIncidenceRightFirstKoszulRestrictIso
    (s : List A) (hs : IsRegular A s) (hZ : IZ = Ideal.ofList s) (b : ℕ) :
    (Koszul.seqComplexTensor s.get AmbientModule).homology b ≅
      (ModuleCat.restrictScalars κ).obj
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b) := by
  let U := (Koszul.seqComplexTensor s.get AmbientModule).homology b
  let V := (ModuleCat.restrictScalars κ).obj
    (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b)
  let e : U ≃ₗ[A] V :=
    { toFun := fun m => m
      invFun := fun m => m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => (correspondenceTripleIncidenceRightFirstKoszulModule_stalkMap_smul
        f g h i z w v x s hs hZ b a m).symm }
  exact e.toModuleIso

/-- The whole remaining Y-column respects the true Z-first stalk quotient map. -/
def correspondenceTripleIncidenceRightAmbientKoszulIsoRemaining
    (t s : List A) (hs : IsRegular A s) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    (Koszul.seqComplexTensor t.get
      ((Koszul.seqComplexTensor s.get AmbientModule).homology b)).homology a ≅
      (ModuleCat.restrictScalars κ).obj
        ((Koszul.seqComplexTensor (fun j => κ (t.get j))
          (correspondenceRightRemainingFirstKoszulModule
            f g h i z w v x s hs hZ b)).homology a) := by
  letI : Algebra A P := (κ).toAlgebra
  exact Koszul.homologyTensorCongr t.get
    (correspondenceTripleIncidenceRightFirstKoszulRestrictIso
      f g h i z w v x s hs hZ b).toLinearEquiv a ≪≫
    Koszul.homologySeqComplexTensorRestrictScalarsIso t.get
      (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b) a

/-- The actual right iterated Tor is remaining homology with the genuine right-stage action. -/
def correspondenceTripleIncidenceRightIteratedTorIsoRemainingKoszul
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b ≅
      (ModuleCat.restrictScalars κ).obj
        ((Koszul.seqComplexTensor (fun j => κ (t.get j))
          (correspondenceRightRemainingFirstKoszulModule
            f g h i z w v x s hs hZ b)).homology a) :=
  correspondenceTripleIncidenceRightIteratedTorIsoAmbientKoszul
    f g h i z w v x t s ht hs hY hZ a b ≪≫
      correspondenceTripleIncidenceRightAmbientKoszulIsoRemaining
        f g h i z w v x t s hs hZ a b

/-- Restricting along the actual surjective right-stage map preserves every column length. -/
theorem length_correspondenceTripleIncidenceRightAmbientKoszul_eq_remaining
    (t s : List A) (hs : IsRegular A s) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    Module.length A
        ((Koszul.seqComplexTensor t.get
          ((Koszul.seqComplexTensor s.get AmbientModule).homology b)).homology a) =
      Module.length P ((Koszul.seqComplexTensor (fun j => κ (t.get j))
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b)).homology a) := by
  let : Algebra A P := (κ).toAlgebra
  let H := (Koszul.seqComplexTensor (fun j => κ (t.get j))
    (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b)).homology a
  let : Module A H := Module.compHom H κ
  have : IsScalarTower A P H := IsScalarTower.of_compHom A P H
  exact (correspondenceTripleIncidenceRightAmbientKoszulIsoRemaining
    f g h i z w v x t s hs hZ a b).toLinearEquiv.length_eq.trans
      (Module.length_eq_of_surjective (M := H)
        (correspondenceTripleIncidenceRightFirstStageStalkMap_surjective f g h i z w v x))

/-- The native right iterated module has its full actual remaining-homology length. -/
theorem length_correspondenceTripleIncidenceRightIteratedTor_eq_remainingKoszul
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    Module.length A (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b) =
      Module.length P ((Koszul.seqComplexTensor (fun j => κ (t.get j))
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b)).homology a) :=
  (length_correspondenceTripleIncidenceRightIteratedTor_eq_ambientKoszul
    f g h i z w v x t s ht hs hY hZ a b).trans
      (length_correspondenceTripleIncidenceRightAmbientKoszul_eq_remaining
        f g h i z w v x t s hs hZ a b)

/-- The actual right-stage Euler characteristic is the unchanged ambient column Euler. -/
theorem seqEuler_correspondenceTripleIncidenceRightAmbient_eq_remaining
    (t s : List A) (hs : IsRegular A s) (hZ : IZ = Ideal.ofList s) (b : ℕ) :
    Koszul.seqEuler t.get ((Koszul.seqComplexTensor s.get AmbientModule).homology b) =
      Koszul.seqEuler (fun j => κ (t.get j))
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b) := by
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro a _
  rw [length_correspondenceTripleIncidenceRightAmbientKoszul_eq_remaining
    f g h i z w v x t s hs hZ a b]

/-- The full signed right iterated coefficient is the literal actual right-stage Euler sum. -/
theorem finsum_signed_rightIteratedTor_eq_sum_remainingFirstEuler
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) :
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length A
        (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x ab.1 ab.2)).toNat : ℤ)) =
      ∑ b : Fin (s.length + 1), (-1 : ℤ) ^ (b : ℕ) *
        Koszul.seqEuler (fun j => κ (t.get j))
          (correspondenceRightRemainingFirstKoszulModule f g h i z w v x s hs hZ b) := by
  rw [finsum_signed_rightIteratedTor_eq_sum_ambientFirstEuler f g h i z w v x t s ht hs hY hZ]
  apply Finset.sum_congr rfl
  intro b _
  rw [seqEuler_correspondenceTripleIncidenceRightAmbient_eq_remaining
    f g h i z w v x t s hs hZ b]

end Stacks.Chow
