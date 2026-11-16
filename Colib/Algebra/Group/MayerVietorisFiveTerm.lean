/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Group.MulExactProduct

/-! # Gluing a two-summand isomorphism by a five-term exact row -/

@[expose] public section

namespace GroupMayerVietoris

/-- The product five lemma for a two-open row
from the local pair and overlap in degree `n + 1` to the global group and
then the local pair and overlap in degree `n`.
The middle conclusion follows from the four actual local comparisons. -/
theorem bijective_of_fiveTerm
    {A B C D E A' B' C' D' E' : Type*}
    [Group A] [Group B] [Group C] [Group D] [Group E]
    [Group A'] [Group B'] [Group C'] [Group D'] [Group E']
    (f : A →* B) (g : B →* C) (h : C →* D) (i : D →* E)
    (f' : A' →* B') (g' : B' →* C') (h' : C' →* D') (i' : D' →* E')
    (a : A × A →* A') (b : B × B →* B') (c : C × C →* C')
    (d : D × D →* D') (e : E × E →* E')
    (hs : Function.MulExact f g ∧ Function.MulExact g h ∧ Function.MulExact h i)
    (ht : Function.MulExact f' g' ∧ Function.MulExact g' h' ∧ Function.MulExact h' i')
    (h₁ : f'.comp a = b.comp (f.prodMap f))
    (h₂ : g'.comp b = c.comp (g.prodMap g))
    (h₃ : h'.comp c = d.comp (h.prodMap h))
    (h₄ : i'.comp d = e.comp (i.prodMap i))
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (hd : Function.Bijective d) (he : Function.Bijective e) : Function.Bijective c :=
  MonoidHom.bijective_of_mulExact_prodMap f g h i f' g' h' i' a b c d e
    h₁ h₂ h₃ h₄ hs.1 hs.2.1 hs.2.2 ht.1 ht.2.1 ht.2.2 ha.surjective hb hd he.injective

end GroupMayerVietoris
