/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Group.Prod

/-! # Products of exact pairs of group homomorphisms

This is the group-theoretic input for taking two copies of a localization or
Mayer–Vietoris sequence. It does not change the original homomorphisms.
-/

@[expose] public section

namespace MonoidHom

/-- Taking two copies of an exact pair preserves exactness on the product. -/
theorem mulExact_prodMap_self {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (h : Function.MulExact f g) :
    Function.MulExact (f.prodMap f) (g.prodMap g) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (h x.1).mp (congrArg Prod.fst hx)
    obtain ⟨b, hb⟩ := (h x.2).mp (congrArg Prod.snd hx)
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨a, rfl⟩
    exact Prod.ext (h.apply_apply_eq_one a.1) (h.apply_apply_eq_one a.2)

/-- The five lemma when the top row is the square of an exact row.

The four outside maps identify the corresponding doubled groups; the middle
map identifies their supported groups. -/
theorem bijective_of_mulExact_prodMap {A B C D E A' B' C' D' E' : Type*}
    [Group A] [Group B] [Group C] [Group D] [Group E]
    [Group A'] [Group B'] [Group C'] [Group D'] [Group E']
    (f : A →* B) (g : B →* C) (h : C →* D) (i : D →* E)
    (f' : A' →* B') (g' : B' →* C') (h' : C' →* D') (i' : D' →* E')
    (a : A × A →* A') (b : B × B →* B') (c : C × C →* C')
    (d : D × D →* D') (e : E × E →* E')
    (h₁ : f'.comp a = b.comp (f.prodMap f))
    (h₂ : g'.comp b = c.comp (g.prodMap g))
    (h₃ : h'.comp c = d.comp (h.prodMap h))
    (h₄ : i'.comp d = e.comp (i.prodMap i))
    (hfg : Function.MulExact f g) (hgh : Function.MulExact g h)
    (hhi : Function.MulExact h i)
    (hfg' : Function.MulExact f' g') (hgh' : Function.MulExact g' h')
    (hhi' : Function.MulExact h' i')
    (ha : Function.Surjective a) (hb : Function.Bijective b)
    (hd : Function.Bijective d) (he : Function.Injective e) : Function.Bijective c :=
  MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f.prodMap f) (g.prodMap g) (h.prodMap h) (i.prodMap i) f' g' h' i'
    a b c d e h₁ h₂ h₃ h₄ (mulExact_prodMap_self f g hfg) (mulExact_prodMap_self g h hgh)
    (mulExact_prodMap_self h i hhi) hfg' hgh' hhi' ha hb hd he

end MonoidHom
