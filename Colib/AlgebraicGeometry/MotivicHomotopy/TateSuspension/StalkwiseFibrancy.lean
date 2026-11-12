/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.PresheafAdjunction
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantSmash

/-!
# The Tate internal Hom and Nisnevich fibrancy

The actual presheaf right adjoint of Tate suspension preserves the lifting
property against Nisnevich stalkwise trivial monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)

/-- The pointed internal Hom from the original Tate quotient preserves Nisnevich fibrancy. -/
theorem isStalkwiseInjectiveFibrant_tatePresheafLoops
    {X : PointedSimplicialPresheaf.{u + 1} Cᵣ}
    (hX : IsStalkwiseInjectiveFibrant Cᵣ Jᵣ X) :
    IsStalkwiseInjectiveFibrant Cᵣ Jᵣ ((tatePresheafLoops R).obj X) :=
  isStalkwiseInjectiveFibrant_rightAdjoint_smash Cᵣ Jᵣ (liftedTateSphere R)
    (tatePresheafAdjunction R) hX

end AlgebraicGeometry.MotivicHomotopy
