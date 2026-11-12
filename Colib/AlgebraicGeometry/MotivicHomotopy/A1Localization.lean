/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.GroupSchemes
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Colib.CategoryTheory.Sites.Simplicial.UniverseLift

/-!
# A¹-localization of smooth Nisnevich presheaves

The interval is the lifted simplicial Yoneda presheaf of the native affine
line. Its pointed cylinder projections supply the local tests.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (S : Scheme.{u})

local notation "Cₛ" => SmoothSite S
local notation "Jₛ" => SmoothSite.nisnevichTopology S

/-- The native affine line as a simplicial presheaf in the coefficient universe. -/
abbrev affineLineInterval : Cₛᵒᵖ ⥤ SSet.{u + 1} :=
  (uliftPresheaf.{u + 1, u} Cₛ).obj
    ((simplicialYoneda Cₛ).obj (SmoothSite.additiveGroupObject S))

/-- The A¹-localization of the smooth Nisnevich homotopy category. -/
abbrev AffineLineHomotopyCategory :=
  IntervalHomotopyCategory Cₛ Jₛ (affineLineInterval S)

/-- The chosen localization functor for the actual affine-line interval. -/
abbrev toAffineLineHomotopyCategory :
    PointedSimplicialPresheaf.{u + 1} Cₛ ⥤ AffineLineHomotopyCategory S :=
  toIntervalHomotopyCategory Cₛ Jₛ (affineLineInterval S)

end AlgebraicGeometry.MotivicHomotopy
