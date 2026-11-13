/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.FiniteOmegaSpectrum
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.OmegaSpectrum
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.StrictRealization
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.StrictLoopComparison
import Colib.Util.References

/-!
# Strict realizations of the motivic coefficient Ω-spectra

The strict Tate prespectra use local fibrant representatives of the
original integral and finite motivic cohomology levels. Their strict
bonding maps recover the signed bonding maps in A¹-homotopy.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

section Strict

variable (R : CommRingCat.{u}) (E : A1TatePrespectrum R)

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)

/-- The actual strict adjoint bond is stalkwise weak when the given
motivic prespectrum satisfies the Ω condition. -/
theorem stalkwiseWeakEquivalences_strictTateRealization_adjointBonding
    (hE : SequentialPrespectrum.IsOmegaSpectrum (motivicTateAdjunction R) E) (i : ℕ) :
    stalkwiseWeakEquivalences Cᵣ Jᵣ
      (SequentialPrespectrum.adjointBonding (tatePresheafAdjunction R)
        (strictTateRealization R E) i) := by
  let X := strictTateRealization R E
  have h : SequentialPrespectrum.IsOmegaSpectrum (motivicTateAdjunction R)
      ((toA1TatePrespectrum R).obj X) :=
    (SequentialPrespectrum.isOmegaSpectrum_iff_of_iso (motivicTateAdjunction R)
      (strictTateRealizationIso R E)).2 hE
  exact stalkwiseWeakEquivalences_tateTranspose R (X.level (i + 1))
    (strictTateRealization_level_isFibrant R E (i + 1))
    (strictTateRealization_level_isLocal R E (i + 1)) (X.level i)
    (strictTateRealization_level_isFibrant R E i) (strictTateRealization_level_isLocal R E i)
    (X.bonding i) (h i)

end Strict

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Rₖ" => CommRingCat.of k

/-- The strict Tate prespectrum with the original integral motivic cohomology levels. -/
@[colib_tag "COL-1117"]
abbrev strictIntegralMotivicTatePrespectrum : TatePrespectrum Rₖ :=
  strictTateRealization Rₖ (integralMotivicTatePrespectrum k)

/-- The strict Tate prespectrum with the original finite motivic coefficient cones. -/
@[colib_tag "COL-1117"]
abbrev strictFiniteMotivicTatePrespectrum (n : ℕ) : TatePrespectrum Rₖ :=
  strictTateRealization Rₖ (finiteMotivicTatePrespectrum k n)

/-- The strict integral construction recovers the signed Tate prespectrum. -/
def strictIntegralMotivicTatePrespectrumIso :
    (toA1TatePrespectrum Rₖ).obj (strictIntegralMotivicTatePrespectrum k) ≅
      integralMotivicTatePrespectrum k :=
  strictTateRealizationIso Rₖ (integralMotivicTatePrespectrum k)

/-- The strict finite construction recovers the signed Tate prespectrum. -/
def strictFiniteMotivicTatePrespectrumIso (n : ℕ) :
    (toA1TatePrespectrum Rₖ).obj (strictFiniteMotivicTatePrespectrum k n) ≅
      finiteMotivicTatePrespectrum k n :=
  strictTateRealizationIso Rₖ (finiteMotivicTatePrespectrum k n)

/-- The localized strict integral prespectrum satisfies the original Ω condition. -/
theorem strictIntegralMotivicTatePrespectrum_isOmegaSpectrum :
    SequentialPrespectrum.IsOmegaSpectrum (motivicTateAdjunction Rₖ)
      ((toA1TatePrespectrum Rₖ).obj (strictIntegralMotivicTatePrespectrum k)) :=
  (SequentialPrespectrum.isOmegaSpectrum_iff_of_iso (motivicTateAdjunction Rₖ)
    (strictIntegralMotivicTatePrespectrumIso k)).2
      (integralMotivicTatePrespectrum_isOmegaSpectrum k)

/-- The localized strict finite prespectrum satisfies the original Ω condition. -/
theorem strictFiniteMotivicTatePrespectrum_isOmegaSpectrum (n : ℕ) :
    SequentialPrespectrum.IsOmegaSpectrum (motivicTateAdjunction Rₖ)
      ((toA1TatePrespectrum Rₖ).obj (strictFiniteMotivicTatePrespectrum k n)) :=
  (SequentialPrespectrum.isOmegaSpectrum_iff_of_iso (motivicTateAdjunction Rₖ)
    (strictFiniteMotivicTatePrespectrumIso k n)).2
      (finiteMotivicTatePrespectrum_isOmegaSpectrum k n)

/-- The integral spectrum's actual strict adjoint bonds are Nisnevich weak equivalences. -/
@[colib_tag "COL-1117"]
theorem stalkwiseWeakEquivalences_strictIntegralMotivicTatePrespectrum_adjointBonding (i : ℕ) :
    stalkwiseWeakEquivalences (SmoothSite (Spec Rₖ)) (SmoothSite.nisnevichTopology (Spec Rₖ))
      (SequentialPrespectrum.adjointBonding (tatePresheafAdjunction Rₖ)
        (strictIntegralMotivicTatePrespectrum k) i) :=
  stalkwiseWeakEquivalences_strictTateRealization_adjointBonding Rₖ
    (integralMotivicTatePrespectrum k) (integralMotivicTatePrespectrum_isOmegaSpectrum k) i

/-- The finite spectrum's actual strict adjoint bonds are Nisnevich weak equivalences. -/
@[colib_tag "COL-1117"]
theorem stalkwiseWeakEquivalences_strictFiniteMotivicTatePrespectrum_adjointBonding (n i : ℕ) :
    stalkwiseWeakEquivalences (SmoothSite (Spec Rₖ)) (SmoothSite.nisnevichTopology (Spec Rₖ))
      (SequentialPrespectrum.adjointBonding (tatePresheafAdjunction Rₖ)
        (strictFiniteMotivicTatePrespectrum k n) i) :=
  stalkwiseWeakEquivalences_strictTateRealization_adjointBonding Rₖ
    (finiteMotivicTatePrespectrum k n) (finiteMotivicTatePrespectrum_isOmegaSpectrum k n) i

/-- The integral spectrum's actual strict adjoint bonds are motivic weak equivalences. -/
theorem intervalWeakEquivalences_strictIntegralMotivicTatePrespectrum_adjointBonding (i : ℕ) :
    intervalWeakEquivalences (SmoothSite (Spec Rₖ)) (SmoothSite.nisnevichTopology (Spec Rₖ))
      (affineLineInterval (Spec Rₖ))
      (SequentialPrespectrum.adjointBonding (tatePresheafAdjunction Rₖ)
        (strictIntegralMotivicTatePrespectrum k) i) :=
  stalkwiseWeakEquivalences_le_intervalWeakEquivalences _ _ _ _
    (stalkwiseWeakEquivalences_strictIntegralMotivicTatePrespectrum_adjointBonding k i)

/-- The finite spectrum's actual strict adjoint bonds are motivic weak equivalences. -/
theorem intervalWeakEquivalences_strictFiniteMotivicTatePrespectrum_adjointBonding (n i : ℕ) :
    intervalWeakEquivalences (SmoothSite (Spec Rₖ)) (SmoothSite.nisnevichTopology (Spec Rₖ))
      (affineLineInterval (Spec Rₖ))
      (SequentialPrespectrum.adjointBonding (tatePresheafAdjunction Rₖ)
        (strictFiniteMotivicTatePrespectrum k n) i) :=
  stalkwiseWeakEquivalences_le_intervalWeakEquivalences _ _ _ _
    (stalkwiseWeakEquivalences_strictFiniteMotivicTatePrespectrum_adjointBonding k n i)

end AlgebraicGeometry.MotivicHomotopy
