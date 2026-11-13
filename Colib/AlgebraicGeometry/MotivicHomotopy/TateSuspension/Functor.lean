/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension
public import Colib.CategoryTheory.Limits.PointedSmashFunctor
public import Colib.CategoryTheory.Sites.Simplicial.UniverseLift

/-!
# Tate suspension on pointed presheaves

Smash on the right with the original pointed Tate quotient, lifted to the
coefficient universe. Both maps out of the actual Tate cone induce
natural transformations of pointed presheaf endofunctors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)

/-- The original Tate quotient lifted to the coefficient universe. -/
abbrev liftedTateSphere : PointedSimplicialPresheaf.{u + 1} Cᵣ :=
  (uliftPointed.{u + 1, u} Cᵣ).obj (tateSphere R)

/-- Tate suspension before localization, formed with the actual pointed smash. -/
def tatePresheafSuspension :
    PointedSimplicialPresheaf.{u + 1} Cᵣ ⥤ PointedSimplicialPresheaf.{u + 1} Cᵣ :=
  Under.smashRightFunctor (liftedTateSphere R)

/-- The natural map of smash functors induced by the cone collapse to the Tate quotient. -/
def tateConeSmashToSphere :
    Under.smashRightFunctor ((uliftPointed.{u + 1, u} Cᵣ).obj (tateCone R)) ⟶
      tatePresheafSuspension R :=
  Under.smashRightBifunctor.map ((uliftPointed.{u + 1, u} Cᵣ).map (tateConeToSphere R))

/-- The natural map induced by collapsing the affine-line term of the Tate cone. -/
def tateConeSmashToTorusSuspension :
    Under.smashRightFunctor ((uliftPointed.{u + 1, u} Cᵣ).obj (tateCone R)) ⟶
      Under.smashRightFunctor ((uliftPointed.{u + 1, u} Cᵣ).obj (simplicialTorusSuspension R)) :=
  Under.smashRightBifunctor.map ((uliftPointed.{u + 1, u} Cᵣ).map (tateConeToSuspension R))

end AlgebraicGeometry.MotivicHomotopy
