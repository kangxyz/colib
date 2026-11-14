/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.FiniteLoopWords
public import Colib.Topology.Prespectrum.LoopTransposeStableSign
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Stable signs of the original finite cyclic and reversal words

The signs follow the literal recursive loop-transpose words. Naturality of
the genuine parameter shift carries scalar identities through the old loop;
no geometric parameter permutation or quotient sign is assumed here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v w
namespace Topology.LoopPrespectrum

private theorem scalar_of_iso {A B : AddCommGrpCat.{w}}
    (q : A ⟶ A) (e : A ≅ B) (r : B ⟶ B) (z : ℤ)
    (he : q ≫ e.hom = e.hom ≫ r) (hr : r = z • 𝟙 B) : q = z • 𝟙 A := by
  apply (cancel_mono e.hom).1
  rw [he, hr]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.comp_id, Category.id_comp]

/-- The genuine parameter shift preserves a scalar action of an actual endomorphism. -/
theorem parameterLoopingMap_stable_scalar {E : LoopPrespectrum.{w}} (f : E ⟶ E)
    (d : ℤ) (z : ℤ) (h : (stableHomotopyFunctor (d + 1)).map f = z • 𝟙 _) :
    (stableHomotopyFunctor d).map (parameterLoopingMap f) = z • 𝟙 _ := by
  exact scalar_of_iso ((stableHomotopyFunctor d).map (parameterLoopingMap f))
    (parameterStableHomotopyIso E d) ((stableHomotopyFunctor (d + 1)).map f) z
    (parameterStableHomotopyIso_naturality f d) h

namespace FiniteLoopWords
open FiniteParameterLooping
variable {C : Type u} [Category.{v} C]

private theorem cyclicIso_succ_app (n : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    (cyclicIso (n + 1) F).hom.app X =
      parameterLoopingMap ((cyclicIso n F).hom.app X) ≫
        LoopTranspose.transpose ((loopDiagram n F).obj X) := rfl

/-- The fixed cyclic word crosses exactly its original number of adjacent loop transposes. -/
theorem cyclicIso_stable_sign (n : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (d : ℤ) :
    (stableHomotopyFunctor d).map ((cyclicIso n F).hom.app X) =
      (-1 : ℤ) ^ n • 𝟙 _ := by
  induction n generalizing d with
  | zero =>
    change (stableHomotopyFunctor d).map (𝟙 _) = _
    simp only [pow_zero, one_smul]
    exact (stableHomotopyFunctor d).map_id _
  | succ n ih =>
    rw [cyclicIso_succ_app, CategoryTheory.Functor.map_comp,
      parameterLoopingMap_stable_scalar _ d _ (ih (d + 1)),
      LoopTranspose.stableHomotopyFunctor_map_transpose]
    change ((-1 : ℤ) ^ n •
      (𝟙 ((stableHomotopyFunctor d).obj ((loopDiagram (n + 1 + 1) F).obj X)))) ≫
        (-𝟙 ((stableHomotopyFunctor d).obj ((loopDiagram (n + 1 + 1) F).obj X))) = _
    simp only [Preadditive.comp_neg, Category.comp_id, pow_succ, mul_neg, mul_one,
      neg_smul]

/-- Reversal of all original loop coordinates has the actual triangular-number sign. -/
theorem reversalIso_stable_sign (n : ℕ) (F : C ⥤ LoopPrespectrum.{w}) (X : C) (d : ℤ) :
    (stableHomotopyFunctor d).map ((reversalIso n F).hom.app X) =
      (-1 : ℤ) ^ (n.choose 2) • 𝟙 _ := by
  induction n generalizing d with
  | zero =>
    change (stableHomotopyFunctor d).map (𝟙 _) = _
    simp only [Nat.choose_zero_succ, pow_zero, one_smul]
    exact (stableHomotopyFunctor d).map_id _
  | succ n ih =>
    change (stableHomotopyFunctor d).map
      (((cyclicIso n F).hom.app X) ≫ parameterLoopingMap ((reversalIso n F).hom.app X)) = _
    rw [CategoryTheory.Functor.map_comp, cyclicIso_stable_sign,
      parameterLoopingMap_stable_scalar _ d _ (ih (d + 1))]
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
      smul_smul, ← pow_add, Nat.choose_succ_succ', Nat.choose_one_right]
    rw [Nat.add_comm (n.choose 2) n]
    rfl

end FiniteLoopWords
end Topology.LoopPrespectrum
