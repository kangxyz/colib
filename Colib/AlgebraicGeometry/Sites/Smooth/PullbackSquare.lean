/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Mathlib.CategoryTheory.Square

/-! # Extracted ordinary primitive with the original parameters and maps -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/PullbackSquare.lean`, blob
`cdcf0b96b44614abf7b9d88f9963b70a96131dd5`.
The actual ordinary free-Yoneda Ext groups, signed boundary and original
restriction arrows are retained. No positive-cohomology sheaf gluing or
whole-cylinder generic-base vanishing is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w t u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}}
  {U X V V' : SmoothSite S} (j : U ⟶ X) (p : V ⟶ X) [IsOpenImmersion j.left]

/-- The actual pullback square, not an abstract replacement diagram. -/
abbrev ordinaryPullbackSquare : Square (SmoothSite S) where
  f₁₂ := pullback.fst j p
  f₁₃ := pullback.snd j p
  f₂₄ := j
  f₃₄ := p
  fac := pullback.condition

end AlgebraicGeometry.Scheme.SmoothSite
