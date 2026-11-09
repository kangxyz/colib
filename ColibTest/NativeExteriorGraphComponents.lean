/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphComponents

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
variable {S : Scheme.{u}} (X Y : SmoothSite S) (φ : X ⟶ Y) (t : genericPoints X.left)

example : exteriorSupport_sourceProjection X Y (nativeGraphComponent X Y φ t) ≫ φ.left =
    exteriorSupport_targetProjection X Y (nativeGraphComponent X Y φ t) :=
  nativeGraphComponent_projection_graph X Y φ t
example : Set.range (exteriorSupport_sourceProjection X Y (nativeGraphComponent X Y φ t)) =
    closure ({t.val} : Set X.left) :=
  nativeGraphComponent_source_range X Y φ t
