/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.StableLocalization
public import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality

/-!
Original exact-functor maps in the constructed spectrum localization, with strict
identity/composition, weak-transformation invariance and original K-map normalization.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/LocalizedFunctoriality.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original normalized exact-functor maps, coherent homotopies and K-map comparison,
including K0, are retained. The native underlying small source is
`WideSubcategory preservesZero` on `SmallWaldhausenCategory`, transported through
`AsSmall`; no replacement prespectrum or strict chosen-zero premise is introduced. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (W : Structure C) (V : Structure D) (U : Structure E)
  {F G : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)

/-- The stable-localization image of the actual original Waldhausen prespectrum. -/
abbrev localizedSpectrum : StableLocalization.{max u v} :=
  toStableLocalization.obj (originalPrespectrum W)

/-- The actual normalized exact-functor map in the constructed stable localization. -/
def localizedSpectrumMap : localizedSpectrum W ⟶ localizedSpectrum V :=
  toStableLocalization.map (exactOriginalPrespectrumMap W V hF)

@[simp] theorem localizedSpectrumMap_id :
    localizedSpectrumMap W W (IsExact.id _ _) = 𝟙 _ :=
  (toStableLocalization_map_eq_of_homotopy (exactOriginalPrespectrumMapIdHomotopy W)).trans
    (toStableLocalization.map_id _)

theorem localizedSpectrumMap_comp {J : D ⥤ E}
    (hJ : IsExact V.cof V.weq U.cof U.weq J) :
    localizedSpectrumMap W U (hF.comp hJ) =
      localizedSpectrumMap W V hF ≫ localizedSpectrumMap V U hJ :=
  (toStableLocalization_map_eq_of_homotopy
    (exactOriginalPrespectrumMapCompHomotopy W V U hF hJ)).trans
      (toStableLocalization.map_comp _ _)

theorem localizedSpectrumMap_weakNatTrans (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) :
    localizedSpectrumMap W V hF = localizedSpectrumMap W V hG :=
  toStableLocalization_map_eq_of_homotopy (exactOriginalPrespectrumHomotopy W V hF hG η hη)

theorem localizedSpectrumMap_iso (e : F ≅ G) :
    localizedSpectrumMap W V hF = localizedSpectrumMap W V hG :=
  toStableLocalization_map_eq_of_homotopy (exactOriginalPrespectrumIsoHomotopy W V hF hG e)

/-- The descended functor gives precisely the existing original exact stable map. -/
@[simp] theorem localizedSpectrumMap_stable_map (d : ℤ) :
    (localizedStableHomotopyFunctor d).map (localizedSpectrumMap W V hF) =
      exactStableKMap W V hF d := rfl

/-- Every original connective K-map, including K0, detects invertibility of this
actual localized spectrum morphism. -/
theorem localizedSpectrumMap_isIso_iff :
    IsIso (localizedSpectrumMap W V hF) ↔ ∀ n : ℕ, Function.Bijective (KMap hF n) :=
  (toStableLocalization_isIso_iff _).trans
    (exactOriginalPrespectrumMap_isStableEquivalence_iff W V hF)

/-- No inverse spectrum-level continuous map is fabricated: the proved stable
equivalence is inverted in the genuine categorical localization. -/
def localizedSpectrumMapIso (h : ∀ n : ℕ, Function.Bijective (KMap hF n)) :
    localizedSpectrum W ≅ localizedSpectrum V :=
  stableLocalizationIso (exactOriginalPrespectrumMap W V hF)
    ((exactOriginalPrespectrumMap_isStableEquivalence_iff W V hF).mpr h)

@[simp] theorem localizedSpectrumMapIso_hom (h : ∀ n : ℕ, Function.Bijective (KMap hF n)) :
    (localizedSpectrumMapIso W V hF h).hom = localizedSpectrumMap W V hF := rfl

/-- The original nonnegative K-map is retained after passing to actual stable morphisms. -/
theorem localizedSpectrumMap_originalK_naturality (n : ℕ) (a : W.K n) :
    originalKStableEquiv V n (Additive.ofMul (KMap hF n a)) =
      (localizedStableHomotopyFunctor (n : ℤ)).map (localizedSpectrumMap W V hF)
        (originalKStableEquiv W n (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality W V hF n a
attribute [colib_tag "COL-0292",
  colib_ref "ThomasonTrobaugh1990" "Sections 1.5.3-1.5.4, pp. 260-261"
    "background" "The connective K-spectrum and its functoriality; the constructed categorical
      localization and the K-zero-inclusive invertibility criterion for this actual map
      are proved here"]
  localizedSpectrumMap_isIso_iff

end CategoryTheory.Waldhausen.IteratedS
