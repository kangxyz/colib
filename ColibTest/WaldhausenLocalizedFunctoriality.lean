/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Colib.KTheory.Waldhausen.Iterated.LocalizedFunctoriality

/-! Proposed, uncompiled regressions for actual original normalized Waldhausen maps.
No strict chosen-zero equation, weakened positive-only K criterion, replacement
prespectrum or continuous inverse is assumed. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum

universe u v

namespace WaldhausenLocalizedFunctorialityTests

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (W : Structure C) (V : Structure D) (U : Structure E)
  {F G : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)

example : StableLocalization.{max u v} := localizedSpectrum W

example : localizedSpectrum W = toStableLocalization.obj (originalPrespectrum W) := rfl

example : localizedSpectrumMap W V hF =
    toStableLocalization.map (exactOriginalPrespectrumMap W V hF) := rfl

example : localizedSpectrumMap W W (IsExact.id _ _) = 𝟙 (localizedSpectrum W) :=
  localizedSpectrumMap_id W

example {J : D ⥤ E} (hJ : IsExact V.cof V.weq U.cof U.weq J) :
    localizedSpectrumMap W U (hF.comp hJ) =
      localizedSpectrumMap W V hF ≫ localizedSpectrumMap V U hJ :=
  localizedSpectrumMap_comp W V U hF hJ

example (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) :
    localizedSpectrumMap W V hF = localizedSpectrumMap W V hG :=
  localizedSpectrumMap_weakNatTrans W V hF hG η hη

example (e : F ≅ G) : localizedSpectrumMap W V hF = localizedSpectrumMap W V hG :=
  localizedSpectrumMap_iso W V hF hG e

-- These are the very same integer stable maps as before localization.
example (d : ℤ) :
    (localizedStableHomotopyFunctor d).map (localizedSpectrumMap W V hF) =
      exactStableKMap W V hF d := localizedSpectrumMap_stable_map W V hF d

example (n : ℕ) (a : W.K n) :
    originalKStableEquiv V n (Additive.ofMul (KMap hF n a)) =
      (localizedStableHomotopyFunctor (n : ℤ)).map (localizedSpectrumMap W V hF)
        (originalKStableEquiv W n (Additive.ofMul a)) :=
  localizedSpectrumMap_originalK_naturality W V hF n a

-- The degree-zero square retains the original KMap, not just an abstract equivalence.
example (a : W.K 0) :
    originalKStableEquiv V 0 (Additive.ofMul (KMap hF 0 a)) =
      (localizedStableHomotopyFunctor 0).map (localizedSpectrumMap W V hF)
        (originalKStableEquiv W 0 (Additive.ofMul a)) :=
  localizedSpectrumMap_originalK_naturality W V hF 0 a

example : IsIso (localizedSpectrumMap W V hF) ↔
    ∀ n : ℕ, Function.Bijective (KMap hF n) := localizedSpectrumMap_isIso_iff W V hF

example (h : IsIso (localizedSpectrumMap W V hF)) : Function.Bijective (KMap hF 0) :=
  (localizedSpectrumMap_isIso_iff W V hF).mp h 0

example (h0 : ¬ Function.Bijective (KMap hF 0)) :
    ¬ IsIso (localizedSpectrumMap W V hF) := by
  intro h
  exact h0 ((localizedSpectrumMap_isIso_iff W V hF).mp h 0)

-- Positive-degree bijectivity needs the separate K0 premise for the converse.
example (h0 : Function.Bijective (KMap hF 0))
    (hpos : ∀ n : ℕ, Function.Bijective (KMap hF (n + 1))) :
    IsIso (localizedSpectrumMap W V hF) := by
  apply (localizedSpectrumMap_isIso_iff W V hF).mpr
  intro n
  cases n with
  | zero => exact h0
  | succ n => exact hpos n

example : IsIso (localizedSpectrumMap W V hF) ↔
    Function.Bijective (KMap hF 0) ∧
      ∀ n : ℕ, Function.Bijective (KMap hF (n + 1)) := by
  constructor
  · intro h
    have hK := (localizedSpectrumMap_isIso_iff W V hF).mp h
    exact ⟨hK 0, fun n ↦ hK (n + 1)⟩
  · rintro ⟨h0, hpos⟩
    apply (localizedSpectrumMap_isIso_iff W V hF).mpr
    intro n
    cases n with
    | zero => exact h0
    | succ n => exact hpos n

variable (h : ∀ n : ℕ, Function.Bijective (KMap hF n))

example : (localizedSpectrumMapIso W V hF h).hom = localizedSpectrumMap W V hF :=
  localizedSpectrumMapIso_hom W V hF h

example : localizedSpectrumMap W V hF ≫ (localizedSpectrumMapIso W V hF h).inv = 𝟙 _ :=
  (localizedSpectrumMapIso W V hF h).hom_inv_id

example : (localizedSpectrumMapIso W V hF h).inv ≫ localizedSpectrumMap W V hF = 𝟙 _ :=
  (localizedSpectrumMapIso W V hF h).inv_hom_id

end WaldhausenLocalizedFunctorialityTests
