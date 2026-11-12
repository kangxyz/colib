/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.SectionKernelBaseChange

/-!
# Tests for actual section kernels under arbitrary base change
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

-- No flatness, smoothness, field, or reducedness hypotheses on the base change.
example {X S T : Scheme.{u}} (q : X ⟶ S) (g : T ⟶ S) [IsSeparated q]
    (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) :
    (Scheme.baseChangedSection q g s hs).ker = s.ker.comap (pullback.fst q g) :=
  Scheme.ker_baseChangedSection q g s hs

example {X S T : Scheme.{u}} (q : X ⟶ S) (g : T ⟶ S)
    (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) :
    Scheme.baseChangedSection q g s hs ≫ pullback.snd q g = 𝟙 T := by simp

-- The same actual positive/negative tensor, with nonflat Cartier pullback allowed.
example {X Y : Scheme.{u}} (f : X ⟶ Y) (D E : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Stacks.Divisors.IsEffectiveCartierDivisor E]
    [Stacks.Divisors.IsPullbackDefined f D] [Stacks.Divisors.IsPullbackDefined f E] :
    Nonempty ((Scheme.Modules.pullback f).obj (Stacks.Divisors.differenceSheaf D E) ≅
      Stacks.Divisors.differenceSheaf (D.comap f) (E.comap f)) :=
  ⟨Stacks.Divisors.differenceSheafPullbackIso f D E⟩

#print axioms Scheme.ker_baseChangedSection
#print axioms Stacks.Divisors.differenceSheafPullbackIso
