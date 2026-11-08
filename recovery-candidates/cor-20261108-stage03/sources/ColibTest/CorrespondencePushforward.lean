/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward

/-! Source-only test candidates. No compilation is claimed. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin Stacks.Chow

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S X Y Z A : Scheme.{u}}

-- The carrier is exactly native AlgebraicCycle, not a new cycle representation.
example (r : X ⟶ Y) [IsFinite r] :
    AlgebraicCycle X ℤ →+ AlgebraicCycle Y ℤ := finiteCyclePushforward r

-- Every point of the fibre appears with its actual residue-field degree.
example (r : X ⟶ Y) [IsFinite r] (c : AlgebraicCycle X ℤ) (y : Y) :
    finiteCyclePushforward r c y =
      ∑ᶠ x ∈ r.base ⁻¹' {y}, c x * (r.residueDegree x : ℤ) :=
  finiteCyclePushforward_apply r c y

-- Signed coefficients and cancellation are included by the native additive homomorphism.
example (r : X ⟶ Y) [IsFinite r] (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward r (-c) = -finiteCyclePushforward r c := map_neg _ _

-- This deliberately imposes no injectivity or distinct-image condition.
example (r : X ⟶ Y) [IsFinite r] (x x' : X) (n m : ℤ)
    (himage : r.base x = r.base x') :
    finiteCyclePushforward r (single x n + single x' m) =
      single (r.base x)
        (n * (r.residueDegree x : ℤ) + m * (r.residueDegree x' : ℤ)) :=
  finiteCyclePushforward_single_add_of_image_eq r x x' n m himage

example (r : X ⟶ Y) (q : Y ⟶ Z) [IsFinite r] [IsFinite q] :
    (finiteCyclePushforward q).comp (finiteCyclePushforward r) =
      finiteCyclePushforward (r ≫ q) := finiteCyclePushforward_comp r q

-- The genuine image support, not merely its set of generic points, is finite.
example (r : A ⟶ X) (p : X ⟶ S)
    [IsFinite (r ≫ p)] [IsSeparated p] [LocallyOfFiniteType p] :
    IsFinite (r.imageι ≫ p) := finiteCyclePushforward_isFinite_imageι_comp r p

-- The nonvertical component-image premise is present in the public endpoint.
example (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsSeparated h] [LocallyOfFiniteType h]
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z)
    (hw : IsFiniteCorrespondencePoint g h w)
    (c : AlgebraicCycle (correspondenceIncidence f g h z w) ℤ)
    (hc : c.support.Finite)
    (hcomp : ∀ t, c t ≠ 0 →
      Set.range ((integralComponentAt t).subschemeι ≫
        correspondenceIncidenceLeft f g h z w) ∈ irreducibleComponents X) :
    finiteCorrespondences f h := incidencePushforward f g h z w hz hw c hc hcomp
