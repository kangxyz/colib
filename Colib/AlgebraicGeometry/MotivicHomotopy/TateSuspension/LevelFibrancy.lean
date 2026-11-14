/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.LevelModel
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.StrictRealization
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Fibrancy in the strict Tate level model

Evaluation preserves the terminal prespectrum, so fibrancy in the projective
level model is precisely the levelwise Nisnevich injective fibrancy already
used to construct strict realizations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf
open CategoryTheory.SequentialPrespectrum AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})
local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Sᵣ" => tatePresheafSuspension R
local notation "Tᵣ" => SequentialPrespectrum Sᵣ

/-- Level-model fibrancy is precisely injective fibrancy of every original level. -/
theorem tateLevelFibrant_iff (E : Tᵣ) :
    letI : HomotopicalAlgebra.ModelCategory Tᵣ := tateLevelModelCategory R
    HomotopicalAlgebra.IsFibrant E ↔ ∀ n, IsStalkwiseInjectiveFibrant Cᵣ Jᵣ (E.level n) := by
  let : HomotopicalAlgebra.ModelCategory Tᵣ := tateLevelModelCategory R
  rw [HomotopicalAlgebra.isFibrant_iff, HomotopicalAlgebra.fibration_iff]
  change tateLevelFibrations R (terminal.from E) ↔ _
  constructor
  · intro h n A B i hi
    let e := ((terminalIsTerminal (C := Tᵣ)).isTerminalObj (evaluation n)).uniqueUpToIso
      ((point_isZero.{u + 1} Cᵣ).isTerminal)
    let α : Arrow.mk ((terminal.from E).app n) ≅ Arrow.mk (toPoint Cᵣ (E.level n)) :=
      Arrow.isoMk (Iso.refl _) e (by
        apply (point_isZero.{u + 1} Cᵣ).isTerminal.hom_ext)
    exact (HasLiftingProperty.iff_of_arrow_iso_right i α).1 (h n i hi)
  · intro h n A B i hi
    let e := ((terminalIsTerminal (C := Tᵣ)).isTerminalObj (evaluation n)).uniqueUpToIso
      ((point_isZero.{u + 1} Cᵣ).isTerminal)
    let α : Arrow.mk ((terminal.from E).app n) ≅ Arrow.mk (toPoint Cᵣ (E.level n)) :=
      Arrow.isoMk (Iso.refl _) e (by
        apply (point_isZero.{u + 1} Cᵣ).isTerminal.hom_ext)
    exact (HasLiftingProperty.iff_of_arrow_iso_right i α).2 (h n i hi)

/-- The existing strict realization is fibrant in the projective level model. -/
theorem strictTateRealization_isLevelFibrant (E : A1TatePrespectrum R) :
    letI : HomotopicalAlgebra.ModelCategory Tᵣ := tateLevelModelCategory R
    HomotopicalAlgebra.IsFibrant (strictTateRealization R E) :=
  (tateLevelFibrant_iff R _).2 (strictTateRealization_level_isFibrant R E)

end AlgebraicGeometry.MotivicHomotopy
