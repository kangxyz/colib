/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Group.MayerVietorisExactRows
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenDerivedImageCoverReflection
public import Colib.AlgebraicGeometry.KTheory.SupportedOpenFineLocalization
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedExcision
public import Colib.AlgebraicGeometry.KTheory.SupportedRestrictionComparison
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula
public import Colib.AlgebraicGeometry.Modules.PerfectRestrictionSquare

/-! # Actual maps for two-open Mayer–Vietoris with auxiliary support -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)

local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "i" => Scheme.Opens.ι T
local notation "b" => Scheme.Opens.ι I₀

local instance supportedMayerVietorisKCommGroup {A B : Scheme.{u}} (k : A ⟶ B)
    [IsOpenImmersion k] (n : ℕ) : CommGroup (PerfectSupportedK k n) :=
  Additivity.KCommGroup (perfectSupportedWaldhausen k) n

/-- Restriction to both members of the cover, in the order `(T,V)`. -/
def restrictionPair (n : ℕ) : PerfectSupportedK Z.ι n →*
    PerfectSupportedK (i ⁻¹ᵁ Z).ι n × PerfectSupportedK (j ⁻¹ᵁ Z).ι n :=
  GroupMayerVietoris.pair (perfectSupportedKRestrict i Z n) (perfectSupportedKRestrict j Z n)

/-- The overlap difference is first restriction times inverse second restriction. -/
def overlapDifference (n : ℕ) :
    PerfectSupportedK (i ⁻¹ᵁ Z).ι n × PerfectSupportedK (j ⁻¹ᵁ Z).ι n →*
      PerfectSupportedK (b ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι n :=
  GroupMayerVietoris.difference (KMap (SupportedOpenDerivedImage.overlapRestrict_exact j T Z) n)
    (perfectSupportedKRestrict b (j ⁻¹ᵁ Z) n)

/-- The two original restriction routes to the overlap commute in all degrees. -/
theorem restriction_square (n : ℕ) :
    (KMap (SupportedOpenDerivedImage.overlapRestrict_exact j T Z) n).comp
      (perfectSupportedKRestrict i Z n) =
    (perfectSupportedKRestrict b (j ⁻¹ᵁ Z) n).comp (perfectSupportedKRestrict j Z n) := by
  unfold perfectSupportedKRestrict
  rw [KMap_comp_KMap, KMap_comp_KMap]
  apply KMap_eq_of_iso _ _
  apply Functor.fullyFaithfulCancelRight ((perfectSupported (b ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι).ι)
  let a := j.resLE T (j ⁻¹ᵁ T) le_rfl
  let : IsOpenImmersion a := by
    dsimp [a]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  exact (Functor.isoWhiskerLeft (perfectSupportedRestrict i Z)
      (perfectSupportedRestrictCongr_comp_ι a (i ⁻¹ᵁ Z)
        (SupportedOpenDerivedImage.coverAuxiliaryPreimage_eq j T Z))) ≪≫
    Functor.isoWhiskerLeft (perfectSupported Z.ι).ι
      (openSquareRestrictCochainIso a b i j (j.resLE_comp_ι le_rfl))

omit [IsOpenImmersion j] in
/-- The support union is exactly the same open after restricting to the second member. -/
theorem fiberOpen_eq :
    j ⁻¹ᵁ (Z ⊔ (i).opensRange) = (j ⁻¹ᵁ Z) ⊔ (b).opensRange := by
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_sup]

variable (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- Excision transports the actual common support along the original restriction. -/
def fiberEquiv (n : ℕ) :
    PerfectSupportedK (Z ⊔ (i).opensRange).ι n ≃*
      PerfectSupportedK ((j ⁻¹ᵁ Z) ⊔ (b).opensRange).ι n := by
  have hc : ∀ x : X, x ∈ Set.range j ∨ x ∈ (Z ⊔ (i).opensRange : X.Opens) := by
    intro x
    rcases hcover x with hx | hx
    · exact Or.inl hx
    · right
      rw [Scheme.Opens.opensRange_ι]
      exact Or.inr hx
  exact (fiberOpen_eq j T Z) ▸ perfectSupportedExcisionKEquiv j (Z ⊔ (i).opensRange) hc n

/-- The actual excision map is literal restriction with the equal union support. -/
theorem fiberEquiv_toMonoidHom (n : ℕ) :
    (fiberEquiv j T Z hcover n).toMonoidHom =
      KMap (perfectSupportedRestrictCongr_exact j (Z ⊔ (i).opensRange)
        (fiberOpen_eq j T Z)) n := by
  unfold fiberEquiv
  generalize fiberOpen_eq j T Z = e
  revert e
  generalize ((j ⁻¹ᵁ Z) ⊔ (b).opensRange) = A
  intro e
  subst A
  rfl

/-- Forgetting the additional support commutes with restriction to the second open. -/
theorem fiberEquiv_comp_union (n : ℕ) :
    (perfectSupportedUnionKMap b (j ⁻¹ᵁ Z) n).comp
      (fiberEquiv j T Z hcover n).toMonoidHom =
    (perfectSupportedKRestrict j Z n).comp (perfectSupportedUnionKMap i Z n) := by
  rw [fiberEquiv_toMonoidHom]
  unfold perfectSupportedUnionKMap perfectSupportedKRestrict
  rw [KMap_comp_KMap, KMap_comp_KMap]
  apply KMap_eq_of_iso _ _
  apply Functor.fullyFaithfulCancelRight ((perfectSupported (j ⁻¹ᵁ Z).ι).ι)
  exact perfectSupportedRestrictCongr_comp_ι j (Z ⊔ (i).opensRange) (fiberOpen_eq j T Z)

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  [QuasiSeparatedSpace V] (hZ : IsCompact (Z : Set X)) [CompactSpace T.toScheme]
  [CompactSpace (j ⁻¹ᵁ T).toScheme]

/-- The transported lower localization boundary, before forgetting support. -/
def lowerBoundary (n : ℕ) :
    PerfectSupportedK (b ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n + 1) →*
      PerfectSupportedK (Z ⊔ (i).opensRange).ι n :=
  (fiberEquiv j T Z hcover n).symm.toMonoidHom.comp
    (perfectSupportedConnectingHomOfUnionCompact b (j ⁻¹ᵁ Z)
      ((isCompact_range ((b).continuous)).union (j.isCompact_preimage hZ)) n)

/-- The canonical Mayer–Vietoris boundary with the prescribed auxiliary support. -/
def connectingHom (n : ℕ) :
    PerfectSupportedK (b ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n + 1) →* PerfectSupportedK Z.ι n :=
  (perfectSupportedUnionKMap i Z n).comp (lowerBoundary j T Z hcover hZ n)

end AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris
