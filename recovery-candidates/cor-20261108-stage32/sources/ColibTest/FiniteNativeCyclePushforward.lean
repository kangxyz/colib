/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Chow.GenericPushforward

open AlgebraicGeometry CategoryTheory TopologicalSpace Function.locallyFinsuppWithin
open Stacks.Chow
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

universe u
variable {X Y Z : Scheme.{u}}

example (f : X ⟶ Y) [IsFinite f] (c : AlgebraicCycle X ℤ) (y : Y) :
    finiteCyclePushforward f c y =
      ∑ᶠ x ∈ f.base ⁻¹' {y}, c x * (f.residueDegree x : ℤ) :=
  finiteCyclePushforward_apply f c y

example (f : X ⟶ Y) [IsFinite f] (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward f (-c) = -finiteCyclePushforward f c := map_neg _ _

example (f : X ⟶ Y) [IsFinite f] (c : AlgebraicCycle X ℤ) (n : ℤ) :
    finiteCyclePushforward f (n • c) = n • finiteCyclePushforward f c := map_zsmul _ _ _

example (f : X ⟶ Y) [IsFinite f] (x : X) :
    finiteCyclePushforward f (single x (-2)) =
      single (f.base x) (-2 * (f.residueDegree x : ℤ)) :=
  finiteCyclePushforward_single f x (-2)

example (f : X ⟶ Y) [IsFinite f] (x x' : X) (h : f.base x = f.base x') :
    finiteCyclePushforward f (single x 3 + single x' (-2)) =
      single (f.base x) (3 * (f.residueDegree x : ℤ) + -2 * (f.residueDegree x' : ℤ)) :=
  finiteCyclePushforward_single_add_of_image_eq f x x' 3 (-2) h

example (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g]
    (c : AlgebraicCycle X ℤ) :
    finiteCyclePushforward g (finiteCyclePushforward f c) =
      finiteCyclePushforward (f ≫ g) c := finiteCyclePushforward_comp_apply f g c

example (i : X ⟶ Y) [IsClosedImmersion i] (c : AlgebraicCycle X ℤ) (x : X) :
    finiteCyclePushforward i c (i.base x) = c x :=
  finiteCyclePushforward_apply_of_isClosedImmersion i c x

example (i : X ⟶ Y) [IsClosedImmersion i] (c d : AlgebraicCycle X ℤ)
    (h : finiteCyclePushforward i c = finiteCyclePushforward i d) : c = d :=
  finiteCyclePushforward_injective_of_isClosedImmersion i h

example (e : X ≅ Y) (c : AlgebraicCycle X ℤ) :
    (finiteCyclePushforwardEquiv e).symm (finiteCyclePushforwardEquiv e c) = c :=
  (finiteCyclePushforwardEquiv e).symm_apply_apply c

example (hfin : (genericPoints X).Finite) (c : genericPoints X → ℤ) :
    finiteCyclePushforward (𝟙 X) (AlgebraicCycle.ofGenericCoefficients hfin c) =
      AlgebraicCycle.ofGenericCoefficients hfin c := finiteCyclePushforward_id _

example (f : X ⟶ Y) [IsFinite f] (hfin : (genericPoints X).Finite)
    (c : genericPoints X → ℤ) :
    (finiteCyclePushforward f (AlgebraicCycle.ofGenericCoefficients hfin c)).support.Finite :=
  finiteCyclePushforward_ofGenericCoefficients_finite_support f hfin c

example (f : X ⟶ Y) [IsFinite f] (hfin : (genericPoints X).Finite)
    (c : genericPoints X → ℤ) (y : Y) :
    finiteCyclePushforward f (AlgebraicCycle.ofGenericCoefficients hfin c) y =
      letI := hfin.fintype
      ∑ x : genericPoints X,
        if y = f.base x.val then c x * (f.residueDegree x.val : ℤ) else 0 :=
  finiteCyclePushforward_ofGenericCoefficients_apply f hfin c y
