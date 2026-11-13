/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.NisnevichFibrantReplacement
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.PresheafAdjunction
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Stalkwise
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseSmashAdjunction

/-!
# The Nisnevich Tate suspension adjunction

Use the actual Nisnevich injective fibrant replacement and the pointed
internal Hom from the original Tate quotient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)

/-- The right adjoint to the original Tate suspension on the smooth
Nisnevich homotopy category. -/
@[no_expose]
def tateStalkwiseLoops :
    StalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ ⥤ StalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ :=
  stalkwiseSmashRightAdjoint.{u + 1} Jᵣ (liftedTateSphere R) (tatePresheafAdjunction R)
    (tateStalkwiseSuspensionCompIso R) (exists_nisnevichInjectiveFibrantReplacement R)

/-- Tate suspension and the original derived pointed internal Hom are adjoint
on the actual smooth Nisnevich homotopy category. -/
@[no_expose]
def tateStalkwiseAdjunction : tateStalkwiseSuspension R ⊣ tateStalkwiseLoops R :=
  stalkwiseSmashAdjunction.{u + 1} Jᵣ (liftedTateSphere R) (tatePresheafAdjunction R)
    (tateStalkwiseSuspensionCompIso R) (exists_nisnevichInjectiveFibrantReplacement R)

end AlgebraicGeometry.MotivicHomotopy
