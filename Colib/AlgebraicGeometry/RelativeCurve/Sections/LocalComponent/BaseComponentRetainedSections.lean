/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.SectionKernelBaseChange

/-! # Original retained sections through the two final curve restrictions

The retained source is pulled back first along the actual curve base change and then along
its component inclusion. The lifted sections recover their original retained morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- Lift an original retained section through the base change and the specified component
factor. The final projection recovers the entire original retained map after base change. -/
theorem exists_baseComponent_retained_section
    {X A Anew Y V : Scheme.{u}} (q : X ⟶ A) (g : Anew ⟶ A)
    (j : Y ⟶ X) (σ : A ⟶ X) (hσ : σ ≫ q = 𝟙 A)
    (σY : A ⟶ Y) (hσY : σY ≫ j = σ)
    (κ : V ⟶ pullback q g) (σV : Anew ⟶ V)
    (hσV : σV ≫ κ = baseChangedSection q g σ hσ) :
    let F := pullback.fst q g
    let jnew := pullback.fst F j
    ∃ σRet : Anew ⟶ pullback κ jnew,
      σRet ≫ pullback.fst κ jnew = σV ∧
      σRet ≫ pullback.snd κ jnew ≫ pullback.snd F j = g ≫ σY := by
  intro F jnew
  have hsq : baseChangedSection q g σ hσ ≫ F = (g ≫ σY) ≫ j := by
    rw [Category.assoc, hσY]
    exact baseChangedSection_fst q g σ hσ
  let σnew := pullback.lift (baseChangedSection q g σ hσ) (g ≫ σY) hsq
  have hκ : σV ≫ κ = σnew ≫ jnew := by
    exact hσV.trans (pullback.lift_fst _ _ _).symm
  refine ⟨pullback.lift σV σnew hκ, pullback.lift_fst _ _ _, ?_⟩
  simp only [pullback.lift_snd_assoc, σnew, pullback.lift_snd]

/-- The original target morphism is unchanged after the two retained pullbacks. -/
theorem baseComponent_retained_target
    {X A Anew Y V T : Scheme.{u}} (q : X ⟶ A) (g : Anew ⟶ A)
    (j : Y ⟶ X) (κ : V ⟶ pullback q g) (σY : A ⟶ Y) (t : Y ⟶ T)
    (σRet : Anew ⟶ pullback κ (pullback.fst (pullback.fst q g) j))
    (hσRet : σRet ≫ pullback.snd κ (pullback.fst (pullback.fst q g) j) ≫
      pullback.snd (pullback.fst q g) j = g ≫ σY) :
    σRet ≫ (pullback.snd κ (pullback.fst (pullback.fst q g) j) ≫
      pullback.snd (pullback.fst q g) j ≫ t) = g ≫ σY ≫ t := by
  simpa only [Category.assoc] using congrArg (fun f => f ≫ t) hσRet

end AlgebraicGeometry.Scheme
