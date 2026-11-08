/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.ClosedImmersionStalk

/-!
# Closed-immersion stalk support with an identified image point

This is the equality-transport form of the native
`Scheme.Hom.ker_stalkMap_le_iff_of_isClosedImmersion`. It retains the literal
stalk map preceded by Mathlib's `stalkCongr`, as used by actual incidence modules.
No quotient ring or substitute local module is introduced.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A prime containing the kernel of the transported actual stalk map has image
in the closed subscheme. The only transport is along the specified point equality. -/
theorem fromSpecStalk_mem_range_of_transported_stalkMap_ker_le
    {T P : Scheme.{u}} (i : T ⟶ P) [IsClosedImmersion i] (x : T) (p : P)
    (e : p = i x) (q : PrimeSpectrum (P.presheaf.stalk p))
    (hq : RingHom.ker
      ((P.presheaf.stalkCongr (.of_eq e)).hom ≫ i.stalkMap x).hom ≤ q.asIdeal) :
    P.fromSpecStalk p q ∈ Set.range i := by
  subst p
  apply (i.ker_stalkMap_le_iff_of_isClosedImmersion x q).mp
  simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using hq

end AlgebraicGeometry.Scheme.Hom
