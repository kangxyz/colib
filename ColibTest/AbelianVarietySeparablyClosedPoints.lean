module

import Colib.AlgebraicGeometry.GroupScheme.AbelianVariety.SeparablyClosedPoints

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

-- The hypothesis is the native class used by the Jacobian and multiplication theorems.
-- Its namesake in Stacks.Groupoids is not an additional hypothesis.
example {k : Type u} [Field k] [IsSepClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A]
    (n : ℕ) (hn : IsUnit (n : k))
    (a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ∃ b : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A), n • b = a :=
  Stacks.Groupoids.exists_nsmul_eq_of_isUnit_of_isSepClosed A n hn a
