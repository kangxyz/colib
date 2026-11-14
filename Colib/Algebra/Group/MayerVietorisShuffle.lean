/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Group.MayerVietorisNaturality

/-! # The product rearrangement for a doubled Mayer–Vietoris row -/

@[expose] public section

namespace GroupMayerVietoris

variable {A B C : Type*} [Group A] [Group B] [CommGroup C]

/-- A doubled pair of restrictions, written with the original local groups first. -/
theorem shuffle_comp_prodMap_pair {D : Type*} [Group D]
    (f : D →* A) (g : D →* B) :
    ((MulEquiv.prodProdProdComm A B A B).toMonoidHom).comp
        ((pair f g).prodMap (pair f g)) =
      pair (f.prodMap f) (g.prodMap g) := rfl

/-- Rearranging the doubled local pair retains the original difference in each coordinate. -/
theorem difference_comp_shuffle (f : A →* C) (g : B →* C) :
    (difference (f.prodMap f) (g.prodMap g)).comp
        (MulEquiv.prodProdProdComm A B A B).toMonoidHom =
      (difference f g).prodMap (difference f g) := rfl

end GroupMayerVietoris
