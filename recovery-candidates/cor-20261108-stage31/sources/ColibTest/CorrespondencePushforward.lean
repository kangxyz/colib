/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward

/-! Native finite pushforward, geometric image and correspondence support checks. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin Stacks.Chow

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S X Y Z A : Scheme.{u}}

-- The carrier is exactly native AlgebraicCycle, not a new cycle representation.
example (r : X ⟶ Y) [IsFinite r] :
    AlgebraicCycle X ℤ →+ AlgebraicCycle Y ℤ := finiteCyclePushforward r

-- The map is definitionally the native constant-weight specialization.
example (r : X ⟶ Y) [IsFinite r] (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward r c =
      AlgebraicCycle.map r (fun _ : X ↦ (0 : ℕ)) (fun _ : Y ↦ (0 : ℕ)) c :=
  finiteCyclePushforward_eq_map r c

example (c : AlgebraicCycle X ℤ) : finiteCyclePushforward (𝟙 X) c = c :=
  finiteCyclePushforward_id c

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

-- Colliding components can cancel even though neither input coefficient vanishes.
example (r : X ⟶ Y) [IsFinite r] (x x' : X) (n m : ℤ)
    (himage : r.base x = r.base x')
    (hweight : n * (r.residueDegree x : ℤ) = m * (r.residueDegree x' : ℤ)) :
    finiteCyclePushforward r (single x n - single x' m) = 0 := by
  rw [map_sub, finiteCyclePushforward_single, finiteCyclePushforward_single,
    himage, hweight, sub_self]

example (r : X ⟶ Y) (q : Y ⟶ Z) [IsFinite r] [IsFinite q] :
    (finiteCyclePushforward q).comp (finiteCyclePushforward r) =
      finiteCyclePushforward (r ≫ q) := finiteCyclePushforward_comp r q

-- The genuine image support, not merely its set of generic points, is finite.
example (r : A ⟶ X) (p : X ⟶ S)
    [IsFinite (r ≫ p)] [IsSeparated p] [LocallyOfFiniteType p] :
    IsFinite (r.imageι ≫ p) := finiteCyclePushforward_isFinite_imageι_comp r p

-- The integral image is the native support at the actual image point.
example (r : A ⟶ X) (p : X ⟶ S)
    [IsSeparated p] [LocallyOfFiniteType p] (a : A)
    (ha : IsFinite (((integralComponentAt a).subschemeι ≫ r) ≫ p)) :
    IsFinite ((integralComponentAt (r.base a)).subschemeι ≫ p) :=
  finiteCyclePushforward_isFinite_integralComponentAt r p a ha

-- Projected images are transported, not replaced by a finiteness assertion.
example (r : A ⟶ X) [IsFinite r] (p : X ⟶ S) (a : A) :
    p.base '' ((integralComponentAt (r.base a)).support : Set X) =
      (r ≫ p).base '' ((integralComponentAt a).support : Set A) :=
  finiteCyclePushforward_projected_support r p a

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
