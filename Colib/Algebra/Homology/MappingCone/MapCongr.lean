/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Congruence on the endpoint maps of a signed mapping cone -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Equal endpoint maps give the same signed cone map. -/
theorem map_congr_endpoints {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') {a a' : K ⟶ K'} {b b' : L ⟶ L'}
    (h : f ≫ b = a ≫ g) (h' : f ≫ b' = a' ≫ g)
    (ha : a = a') (hb : b = b') :
    map f g a b h = map f g a' b' h' := by
  subst a'
  subst b'
  rfl

end CochainComplex.mappingCone
