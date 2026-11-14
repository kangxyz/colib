/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.SupportedMayerVietorisMaps
public import Colib.KTheory.Waldhausen.Fibration.ConnectingNaturality

/-! # The actual localization boundary under a two-open cover with support -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)

local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "i" => Scheme.Opens.ι T
local notation "b" => Scheme.Opens.ι I₀
local notation "a" => Scheme.Hom.resLE j T I₀ le_rfl
local notation "Z'" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) Z
local notation "S" => Z ⊔ Scheme.Hom.opensRange i
local notation "S'" => (Z') ⊔ Scheme.Hom.opensRange b

local instance supportedMayerVietorisBoundaryOverlapOpen : IsOpenImmersion a := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

local notation "F" => perfectSupportedRestrict j Z
local notation "G" => SupportedOpenDerivedImage.overlapRestrict j T Z
local notation "Fₛ" => perfectSupportedRestrictCongr j S (fiberOpen_eq j T Z)

/-- The actual supported restriction functors commute on the overlap. -/
def restrictionSquareIso :
    perfectSupportedRestrict i Z ⋙ G ≅ F ⋙ perfectSupportedRestrict b Z' :=
  Functor.fullyFaithfulCancelRight ((perfectSupported (b ⁻¹ᵁ Z').ι).ι)
    ((Functor.isoWhiskerLeft (perfectSupportedRestrict i Z)
      (perfectSupportedRestrictCongr_comp_ι a (i ⁻¹ᵁ Z)
        (SupportedOpenDerivedImage.coverAuxiliaryPreimage_eq j T Z))) ≪≫
    Functor.isoWhiskerLeft (perfectSupported Z.ι).ι
      (openSquareRestrictCochainIso a b i j (j.resLE_comp_ι le_rfl)))

/-- The second-member restriction is exact also for the overlap-detected weak equivalences. -/
theorem relativeRestrict_exact :
    IsExact (perfectSupportedOpenNested i Z).coarse.cof (perfectSupportedOpenNested i Z).coarse.weq
      (perfectSupportedOpenNested b Z').coarse.cof (perfectSupportedOpenNested b Z').coarse.weq F
    where
  zero := (perfectSupportedRestrict_exact j Z).zero
  cofibration := (perfectSupportedRestrict_exact j Z).cofibration
  pushout := (perfectSupportedRestrict_exact j Z).pushout
  weak f h := by
    let W := perfectSupportedWaldhausen (b ⁻¹ᵁ Z').ι
    change W.weq ((F ⋙ perfectSupportedRestrict b Z').map f)
    have h' : W.weq ((perfectSupportedRestrict i Z ⋙ G).map f) :=
      (SupportedOpenDerivedImage.overlapRestrict_exact j T Z).weak _ h
    let e := (restrictionSquareIso j T Z).symm
    let hArrow : Arrow.mk ((F ⋙ perfectSupportedRestrict b Z').map f) ≅
        Arrow.mk ((perfectSupportedRestrict i Z ⋙ G).map f) :=
      Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality f).symm
    exact (W.weq.arrow_mk_iso_iff hArrow).2 h'

local notation "N" => perfectSupportedOpenNested i Z
local notation "M" => perfectSupportedOpenNested b Z'
local notation "hf" => perfectSupportedRestrict_exact j Z
local notation "hc" => relativeRestrict_exact j T Z
local notation "hₛ" => perfectSupportedRestrictCongr_exact j S (fiberOpen_eq j T Z)

/-- The actual flattening of the acyclic subcategory intertwines the common support restriction. -/
def relativeAcyclicRestrictionIso :
    perfectSupportedOpenAcyclicToSupported i Z ⋙ Fₛ ≅
      acyclicFunctor N M hc ⋙ perfectSupportedOpenAcyclicToSupported b Z' :=
  Functor.fullyFaithfulCancelRight ((perfectSupported (Scheme.Opens.ι S')).ι)
    (Functor.isoWhiskerLeft (perfectSupportedOpenAcyclicToSupported i Z)
      (perfectSupportedRestrictCongr_comp_ι j S (fiberOpen_eq j T Z)))

/-- Actual relative supported restriction commutes with the original relative boundary. -/
theorem relativeConnecting_natural (n : ℕ) :
    (KMap hₛ n).comp (perfectSupportedOpenConnectingHom i Z n) =
      (perfectSupportedOpenConnectingHom b Z' n).comp (KMap hc (n + 1)) := by
  have hflat :
      (KMap hₛ n).comp (perfectSupportedOpenAcyclicSupportedKEquiv i Z n).toMonoidHom =
        (perfectSupportedOpenAcyclicSupportedKEquiv b Z' n).toMonoidHom.comp
          (KMap (acyclicFunctor_exact N M hf hc) n) := by
    rw [perfectSupportedOpenAcyclicSupportedKEquiv_toMonoidHom,
      perfectSupportedOpenAcyclicSupportedKEquiv_toMonoidHom, KMap_comp_KMap, KMap_comp_KMap]
    exact KMap_eq_of_iso _ _ (relativeAcyclicRestrictionIso j T Z) n
  refine MonoidHom.ext fun x => ?_
  let δ := changeWeakConnectingHom N
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence i Z) n
  let δ' := changeWeakConnectingHom M
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence b Z') n
  change KMap hₛ n (perfectSupportedOpenAcyclicSupportedKEquiv i Z n (δ x)) =
    perfectSupportedOpenAcyclicSupportedKEquiv b Z' n (δ' (KMap hc (n + 1) x))
  exact (DFunLike.congr_fun hflat (δ x)).trans
    (congrArg (perfectSupportedOpenAcyclicSupportedKEquiv b Z' n)
      (DFunLike.congr_fun (changeWeakConnectingHom_natural N M hf hc
        (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence i Z)
        (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence b Z') n) x))

/-- The same relative square commutes after passing to the genuine fine open groups. -/
theorem relativeRestriction_natural (n : ℕ) :
    (perfectSupportedOpenKRestrict b Z' n).comp (KMap hc n) =
      (KMap (SupportedOpenDerivedImage.overlapRestrict_exact j T Z) n).comp
        (perfectSupportedOpenKRestrict i Z n) := by
  unfold perfectSupportedOpenKRestrict
  erw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (restrictionSquareIso j T Z).symm n

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  [QuasiSeparatedSpace V] (hZ : IsCompact (Z : Set X)) [CompactSpace T.toScheme]
  [CompactSpace (j ⁻¹ᵁ T).toScheme]

local notation "hX" => IsCompact.union (isCompact_range (Scheme.Hom.continuous i)) hZ
local notation "hV" => IsCompact.union (isCompact_range (Scheme.Hom.continuous b))
    (Scheme.Hom.isCompact_preimage j hZ)

include hZ in
/-- The canonical fine supported localization boundaries commute on the original square. -/
theorem fineConnecting_natural (n : ℕ) :
    (KMap hₛ n).comp (perfectSupportedConnectingHomOfUnionCompact i Z hX n) =
      (perfectSupportedConnectingHomOfUnionCompact b Z' hV n).comp
        (KMap (SupportedOpenDerivedImage.overlapRestrict_exact j T Z) (n + 1)) := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ :=
    (perfectSupportedOpenKRestrict_succ_bijective_of_union_compact i Z hX n).surjective x
  have h₁ := DFunLike.congr_fun
    (perfectSupportedConnectingHomOfUnionCompact_comp_relative i Z hX n) y
  have h₂ := DFunLike.congr_fun (relativeConnecting_natural j T Z n) y
  have h₃ := DFunLike.congr_fun (relativeRestriction_natural j T Z (n + 1)) y
  have h₄ := DFunLike.congr_fun
    (perfectSupportedConnectingHomOfUnionCompact_comp_relative b Z' hV n)
    (KMap hc (n + 1) y)
  exact (congrArg (KMap hₛ n) h₁).trans (h₂.trans (h₄.symm.trans
    (congrArg (perfectSupportedConnectingHomOfUnionCompact b Z' hV n) h₃)))

end AlgebraicGeometry.Scheme.Modules.SupportedMayerVietoris
