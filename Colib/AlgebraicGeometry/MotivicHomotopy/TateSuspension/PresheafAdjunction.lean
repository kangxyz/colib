/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Functor
public import Colib.CategoryTheory.Limits.PointedSmashAdjunction
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The Tate suspension adjunction on pointed simplicial presheaves

The right adjoint is the pointed internal Hom from the original Tate quotient.
The construction uses the closed structure in the coefficient universe.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

attribute [local instance] Functor.functorCategoryMonoidalClosed

/-- The pointed internal Hom from the original Tate quotient. -/
@[no_expose]
def tatePresheafLoops :
    PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R)) ⥤
      PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R)) :=
  Under.pointedIhomFunctor (liftedTateSphere R)

/-- The strict Tate suspension and its right adjoint on pointed simplicial presheaves. -/
@[no_expose]
def tatePresheafAdjunction : tatePresheafSuspension R ⊣ tatePresheafLoops R :=
  Under.smashRightAdjunction (liftedTateSphere R)

end AlgebraicGeometry.MotivicHomotopy
