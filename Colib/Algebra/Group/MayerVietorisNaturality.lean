/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Group.MayerVietoris

/-! # Naturality of the two-open restriction pair and overlap difference -/

@[expose] public section

namespace GroupMayerVietoris

/-- Two restriction squares combine in the original first-then-second order. -/
theorem pair_natural {A B C A' B' C' : Type*}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    (f : A →* B) (g : A →* C) (f' : A' →* B') (g' : A' →* C')
    (a : A →* A') (b : B →* B') (c : C →* C')
    (hf : f'.comp a = b.comp f) (hg : g'.comp a = c.comp g) :
    (pair f' g').comp a = (b.prodMap c).comp (pair f g) :=
  MonoidHom.ext fun x => Prod.ext (DFunLike.congr_fun hf x) (DFunLike.congr_fun hg x)

/-- Two overlap squares combine without changing the first-minus-second convention. -/
theorem difference_natural {A B C A' B' C' : Type*}
    [Group A] [Group B] [CommGroup C] [Group A'] [Group B'] [CommGroup C']
    (f : A →* C) (g : B →* C) (f' : A' →* C') (g' : B' →* C')
    (a : A →* A') (b : B →* B') (c : C →* C')
    (hf : f'.comp a = c.comp f) (hg : g'.comp b = c.comp g) :
    (difference f' g').comp (a.prodMap b) = c.comp (difference f g) := by
  refine MonoidHom.ext fun x => ?_
  change f' (a x.1) * (g' (b x.2))⁻¹ = c (f x.1 * (g x.2)⁻¹)
  rw [map_mul, map_inv]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hf x.1)
    (congrArg Inv.inv (DFunLike.congr_fun hg x.2))

end GroupMayerVietoris
