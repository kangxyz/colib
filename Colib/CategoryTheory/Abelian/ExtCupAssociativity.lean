module

public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct

/-!
# Associativity of the native Ext cup product

The comparison is the original monoidal associator. No derived tensor replacement is used.
-/

@[expose] public noncomputable section

universe w v u

namespace Stacks.ExtCup

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{w} C]
  [EnoughInjectives C]
  {F G H : C}
  [(tensorRight G).Additive] [PreservesFiniteLimits (tensorRight G)]
  [PreservesFiniteColimits (tensorRight G)]
  [(tensorRight H).Additive] [PreservesFiniteLimits (tensorRight H)]
  [PreservesFiniteColimits (tensorRight H)]
  [(tensorRight (G ⊗ H)).Additive] [PreservesFiniteLimits (tensorRight (G ⊗ H))]
  [PreservesFiniteColimits (tensorRight (G ⊗ H))]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Tensoring an extension twice agrees with tensoring by the tensor product, through the
native associator and left unitor. -/
theorem tensorRight_comp_leftUnitor {i : ℕ} (a : Ext.{w} (𝟙_ C) F i) :
    ((Ext.mk₀ ((λ_ G).inv ▷ H)).comp
      ((a.mapExactFunctor (tensorRight G)).mapExactFunctor (tensorRight H)) (zero_add i)).comp
        (Ext.mk₀ (α_ F G H).hom) (add_zero i) =
      (Ext.mk₀ (λ_ (G ⊗ H)).inv).comp
        (a.mapExactFunctor (tensorRight (G ⊗ H))) (zero_add i) := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
    (tensorRightTensor G H).inv (𝟙_ C) i a
  rw [← Stacks.ExtFunctorial.mapExactFunctor_comp_functor] at key
  simp only [tensorRightTensor_inv_app] at key
  rw [Ext.comp_assoc_of_third_deg_zero, ← key,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  congr 2
  exact (leftUnitor_tensor_inv G H).symm

omit [EnoughInjectives C] in
/-- The native cup with the identity pairing is its two defining extension factors. -/
theorem cup_id_pairing {i j n : ℕ} (a : Ext.{w} (𝟙_ C) F i)
    (b : Ext.{w} (𝟙_ C) G j) (h : j + i = n) :
    cup (𝟙 (F ⊗ G)) a b h =
      (b.comp (Ext.mk₀ (λ_ G).inv) (add_zero j)).comp
        (a.mapExactFunctor (tensorRight G)) h := by
  unfold cup
  exact congrArg (fun x => (b.comp (Ext.mk₀ (λ_ G).inv) (add_zero j)).comp x h)
    (Ext.comp_mk₀_id (a.mapExactFunctor (tensorRight G)))

set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the native cup product, with the coefficient associator displayed. -/
theorem cup_assoc {i j k n : ℕ} (a : Ext.{w} (𝟙_ C) F i)
    (b : Ext.{w} (𝟙_ C) G j) (c : Ext.{w} (𝟙_ C) H k)
    (h : k + (j + i) = n) :
    (cup (𝟙 ((F ⊗ G) ⊗ H)) (cup (𝟙 (F ⊗ G)) a b rfl) c h).comp
      (Ext.mk₀ (α_ F G H).hom) (add_zero n) =
    cup (𝟙 (F ⊗ (G ⊗ H))) a (cup (𝟙 (G ⊗ H)) b c rfl)
      (show k + j + i = n by omega) := by
  simp only [cup_id_pairing, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  conv_lhs => simp only [Ext.comp_assoc_of_third_deg_zero]
  rw [Ext.comp_assoc_of_second_deg_zero (b.mapExactFunctor (tensorRight H))]
  have key : (Ext.mk₀ ((tensorRight H).map (λ_ G).inv)).comp
      (((a.mapExactFunctor (tensorRight G)).mapExactFunctor (tensorRight H)).comp
        (Ext.mk₀ (α_ F G H).hom) (add_zero i)) (zero_add i) =
      (Ext.mk₀ (λ_ (G ⊗ H)).inv).comp
        (a.mapExactFunctor (tensorRight (G ⊗ H))) (zero_add i) := by
    have e := tensorRight_comp_leftUnitor (G := G) (H := H) a
    rw [Ext.comp_assoc_of_third_deg_zero] at e
    exact e
  rw [key]
  rw [Ext.comp_assoc_of_second_deg_zero
    ((c.comp (Ext.mk₀ (λ_ H).inv) (add_zero k)).comp
      (b.mapExactFunctor (tensorRight H)) rfl)]
  exact (Ext.comp_assoc (c.comp (Ext.mk₀ (λ_ H).inv) (add_zero k))
    (b.mapExactFunctor (tensorRight H))
    ((Ext.mk₀ (λ_ (G ⊗ H)).inv).comp
      (a.mapExactFunctor (tensorRight (G ⊗ H))) (zero_add i))
    rfl rfl (by omega)).symm

/-- Associativity with arbitrary named degree sums, for applications with fixed placements. -/
theorem cup_assoc_of_eq {i j k ij jk n : ℕ} (a : Ext.{w} (𝟙_ C) F i)
    (b : Ext.{w} (𝟙_ C) G j) (c : Ext.{w} (𝟙_ C) H k)
    (hij : j + i = ij) (hjk : k + j = jk) (hl : k + ij = n) (hr : jk + i = n) :
    (cup (𝟙 ((F ⊗ G) ⊗ H)) (cup (𝟙 (F ⊗ G)) a b hij) c hl).comp
      (Ext.mk₀ (α_ F G H).hom) (add_zero n) =
    cup (𝟙 (F ⊗ (G ⊗ H))) a (cup (𝟙 (G ⊗ H)) b c hjk) hr := by
  subst ij
  subst jk
  exact cup_assoc a b c hl

end Stacks.ExtCup
