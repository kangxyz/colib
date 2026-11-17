/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.ExtCupAssociativity

/-! # Associativity of the native Ext cup with a coefficient pairing -/

@[expose] public noncomputable section
universe w v u
namespace Stacks.ExtCup
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [HasExt.{w} C] [EnoughInjectives C] {F G H T : C}
  [(tensorRight G).Additive] [PreservesFiniteLimits (tensorRight G)]
  [PreservesFiniteColimits (tensorRight G)]
  [(tensorRight H).Additive] [PreservesFiniteLimits (tensorRight H)]
  [PreservesFiniteColimits (tensorRight H)]
  [(tensorRight (G ⊗ H)).Additive] [PreservesFiniteLimits (tensorRight (G ⊗ H))]
  [PreservesFiniteColimits (tensorRight (G ⊗ H))]

/-- Reassociate the native cup and then apply the original first coefficient pairing. -/
theorem cup_assoc_pairing {i j k ij jk n : ℕ} (μ : F ⊗ G ⟶ T)
    (a : Ext.{w} (𝟙_ C) F i) (b : Ext.{w} (𝟙_ C) G j) (c : Ext.{w} (𝟙_ C) H k)
    (hij : j + i = ij) (hjk : k + j = jk) (hl : k + ij = n) (hr : jk + i = n) :
    cup ((α_ F G H).inv ≫ μ ▷ H) a (cup (𝟙 (G ⊗ H)) b c hjk) hr =
      cup (𝟙 (T ⊗ H)) (cup μ a b hij) c hl := by
  have hs := cup_assoc_of_eq a b c hij hjk hl hr
  have hp := congrArg (fun z => z.comp
    (Ext.mk₀ ((α_ F G H).inv ≫ μ ▷ H)) (Nat.add_zero n)) hs
  simp only [Iso.hom_inv_id_assoc, cup_comp_mk₀, Category.id_comp] at hp
  have hμ : (cup (𝟙 (F ⊗ G)) a b hij).comp (Ext.mk₀ μ) (Nat.add_zero ij) =
      cup μ a b hij := by rw [cup_comp_mk₀, Category.id_comp]
  have hleft := comp_mk₀_cup hl μ (𝟙 (T ⊗ H)) (cup (𝟙 (F ⊗ G)) a b hij) c
  rw [hμ, Category.comp_id] at hleft
  exact hp.symm.trans hleft.symm

end Stacks.ExtCup
end
