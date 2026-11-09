/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Graph.Components

/-!
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]

example (t : genericPoints X) :
    IsFiniteCorrespondencePoint f g (correspondenceGraphMap f g φ hφ t.val) :=
  isFiniteCorrespondencePoint_graphMap f g φ hφ t

example (hX : (genericPoints X).Finite) :
    (graphCorrespondenceOfComponents f g φ hφ hX).1 =
      ∑ t ∈ hX.toFinset, single (correspondenceGraphMap f g φ hφ t) 1 :=
  graphCorrespondenceOfComponents_coe f g φ hφ hX

example [IsEmpty X] (hX : (genericPoints X).Finite) :
    graphCorrespondenceOfComponents f g φ hφ hX = 0 :=
  graphCorrespondenceOfComponents_eq_zero_of_isEmpty f g φ hφ hX

end Stacks.Chow
