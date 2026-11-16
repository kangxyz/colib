/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Group.MayerVietoris
public import Mathlib.Algebra.Exact.Basic

/-! # Exact rows for the Mayer–Vietoris gluing argument -/

@[expose] public section

namespace GroupMayerVietoris

variable {A B C D E C' D' E' : Type*}
  [Group A] [Group B] [Group C] [Group D] [CommGroup E]
  [Group C'] [Group D'] [CommGroup E']

/-- The three exact positions of a Mayer–Vietoris row from its two localization rows.
The last position uses reflection of the actual local restriction image; the
positive-degree local-boundary argument is another way to supply that position. -/
theorem exact_fiveTerm_of_image_reflection
    (h : A →* B) (f : B →* C) (g : B →* D) (u : C →* E) (v : D →* E)
    (p : C' →* A) (q : E' →* A) (u' : C' →* E') (v' : D' →* E')
    (hh : h.range = f.ker) (hg : (g.comp h).range = v.ker)
    (hq : q.range = (g.comp h).ker)
    (hp : p.range = h.ker) (hv' : v'.range = q.ker)
    (hqu : q.comp u' = p) (hcomm : u.comp f = v.comp g)
    (hreflect : ∀ c, u c ∈ v.range → c ∈ f.range) :
    Function.MulExact (difference u' v') (h.comp q) ∧
      Function.MulExact (h.comp q) (pair f g) ∧
      Function.MulExact (pair f g) (difference u v) :=
  ⟨MonoidHom.mulExact_iff.mpr
    (range_difference_eq_ker_boundary h p q u' v' hp hv' hqu).symm,
    MonoidHom.mulExact_iff.mpr (range_boundary_eq_ker_pair h q f g hh hq).symm,
    MonoidHom.mulExact_iff.mpr
      (range_pair_eq_ker_difference_of_image_reflection h f g u v hh hg hcomm hreflect).symm⟩

end GroupMayerVietoris
