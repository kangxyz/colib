/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.A1Localization
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Stalkwise
public import Colib.CategoryTheory.Sites.Simplicial.IntervalAdjunction
import Colib.CategoryTheory.Sites.Simplicial.SmashCylinder

/-!
# Localizing Tate suspension

The cylinder comparison and a stalkwise adjunction give descent of the
Tate smash functor to the chosen A¹-localization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Qᵢ" => toAffineLineHomotopyCategory (Spec R)
local notation "Wᵢ" => intervalWeakEquivalences Cᵣ Jᵣ (affineLineInterval (Spec R))

/-- Tate suspension sends the original A¹-cylinder projection to an A¹-weak equivalence. -/
theorem intervalWeakEquivalences_tatePresheafSuspension_map_cylinderProjection
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) :
    Wᵢ ((tatePresheafSuspension R).map (cylinderProjection X (affineLineInterval (Spec R)))) :=
  intervalWeakEquivalences_smashRightFunctor_map_cylinderProjection Jᵣ
    (affineLineInterval (Spec R)) X (liftedTateSphere R)

variable {Ω : StalkwiseHomotopyCategory.{u + 1} (SmoothSite (Spec R))
    (SmoothSite.nisnevichTopology (Spec R)) ⥤ StalkwiseHomotopyCategory.{u + 1}
      (SmoothSite (Spec R)) (SmoothSite.nisnevichTopology (Spec R))}
  (adj : tateStalkwiseSuspension R ⊣ Ω)

include adj

/-- A stalkwise right adjoint to Tate suspension preserves A¹-locality. -/
theorem isA1Local_tateRightAdjoint {L : StalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ}
    (hL : IsIntervalLocal Cᵣ Jᵣ (affineLineInterval (Spec R)) L) :
    IsIntervalLocal Cᵣ Jᵣ (affineLineInterval (Spec R)) (Ω.obj L) :=
  isIntervalLocal_rightAdjoint Cᵣ Jᵣ (tateStalkwiseSuspensionCompIso R) adj
    (affineLineInterval (Spec R))
    (intervalWeakEquivalences_tatePresheafSuspension_map_cylinderProjection R) hL

private theorem tateA1Inverts : (Wᵢ).IsInvertedBy (tatePresheafSuspension R ⋙ Qᵢ) :=
  fun _ _ f hf ↦ (Wᵢ).Q_inverts _ (intervalWeakEquivalences_map_of_stalkwiseAdjunction
    Cᵣ Jᵣ (tateStalkwiseSuspensionCompIso R) adj (affineLineInterval (Spec R))
    (intervalWeakEquivalences_tatePresheafSuspension_map_cylinderProjection R) f hf)

/-- Given the stalkwise adjunction, Tate suspension on the chosen A¹-homotopy category. -/
@[no_expose]
def tateA1Suspension : AffineLineHomotopyCategory (Spec R) ⥤ AffineLineHomotopyCategory (Spec R) :=
  Localization.lift (tatePresheafSuspension R ⋙ Qᵢ) (tateA1Inverts R adj) Qᵢ

/-- The A¹-localized functor retains the original presheaf suspension maps. -/
@[no_expose]
def tateA1SuspensionCompIso : Qᵢ ⋙ tateA1Suspension R adj ≅ tatePresheafSuspension R ⋙ Qᵢ :=
  Localization.fac (tatePresheafSuspension R ⋙ Qᵢ) (tateA1Inverts R adj) Qᵢ

end AlgebraicGeometry.MotivicHomotopy
