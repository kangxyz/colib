/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Scheme.GenericPointsOfGeometricallyIrreducible

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section
universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f]
  (hf : IsOpenMap f)

example (y : genericPoints Y) :
    f (f.genericPointsEquivOfGeometricallyIrreducible hf y).val = y.val :=
  f.genericPointsEquivOfGeometricallyIrreducible_apply hf y

example (y : genericPoints Y) :
    closure ({(f.genericPointsEquivOfGeometricallyIrreducible hf y).val} : Set X) =
      f ⁻¹' closure ({y.val} : Set Y) :=
  f.genericPointsEquivOfGeometricallyIrreducible_closure hf y

example (x x' : genericPoints X) (h : f x.val = f x'.val) : x = x' :=
  f.genericPoints_injective_of_geometricallyIrreducible hf h
