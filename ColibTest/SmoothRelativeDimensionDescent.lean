/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Morphisms.Smooth.RelativeDimensionDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- The actual first pullback projection supplies the descended relative-curve condition. -/
example {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [Smooth f] [Surjective g] [SmoothOfRelativeDimension 1 (pullback.snd f g)] :
    SmoothOfRelativeDimension 1 f :=
  SmoothOfRelativeDimension.of_surjective_isPullback
    (pullback.fst f g) (pullback.snd f g) f g (IsPullback.of_hasPullback f g) 1

/-- Empty sources are included: the criterion does not add a nonemptiness assumption. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsEmpty X] (n : ℕ) :
    SmoothOfRelativeDimension n f :=
  Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f n (fun x => isEmptyElim x)
