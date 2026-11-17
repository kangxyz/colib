/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.OrderedMilnorKummer
public import Colib.AlgebraicGeometry.EtaleCohomology.OrderedKummerProduct
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Product

/-! # Compatibility of the ordinary Kummer symbol with the native Milnor product -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MonoidalCategory
universe u
set_option maxRecDepth 4096
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
namespace AlgebraicGeometry.EtaleCohomology.MilnorKummer
variable (k : Type u) [Field k]

/-- The existing graded Milnor product, merely packaged as a biadditive map. -/
def nativeMilnorProductHom (p q : ℕ) :
    MilnorKTheory k p →+ MilnorKTheory k q →+ MilnorKTheory k (p + q) :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
    (fun y => GradedMonoid.GMul.mul x y) (by
      intro y z
      apply Subtype.ext
      exact mul_add (x : MilnorKRing k) (y : MilnorKRing k) (z : MilnorKRing k))) (by
    intro x y
    apply AddMonoidHom.ext
    intro z
    apply Subtype.ext
    exact add_mul (x : MilnorKRing k) (y : MilnorKRing k) (z : MilnorKRing k))

/-- Biadditive packaging changes none of the native graded product's values. -/
theorem nativeMilnorProductHom_apply (p q : ℕ)
    (x : MilnorKTheory k p) (y : MilnorKTheory k q) :
    nativeMilnorProductHom k p q x y = GradedMonoid.GMul.mul x y := rfl

variable (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The ordered field-unit cup carries tuple concatenation to the native coefficient product. -/
theorem orderedFieldKummerCup_append (p q : ℕ) (a : Fin p → kˣ) (b : Fin q → kˣ) :
    orderedFieldKummerCup k n (p + q) (Fin.append a b) =
      Stacks.Kummer.rootsOfUnityPowerProductHom (𝟙 (Spec (.of k))) n p q
        (orderedFieldKummerCup k n p a) (orderedFieldKummerCup k n q b) := by
  let g : kˣ → Stacks.Kummer.unitsModuloPowers (Spec (.of k)) n :=
    fun x => fieldUnitModuloPowers k n (Additive.ofMul x)
  have h : (fun i => g (Fin.append a b i)) =
      Fin.append (fun i => g (a i)) (fun i => g (b i)) := by
    funext i
    induction i using Fin.addCases <;> simp
  change Stacks.Kummer.orderedKummerCup _ _ _ _ (fun i => g (Fin.append a b i)) = _
  rw [h]
  exact Stacks.Kummer.orderedKummerCup_append _ _ _ _ _ _ _

/-- In every pair of degrees, the ordinary Kummer symbol preserves the native Milnor product. -/
@[colib_tag "COL-1301"]
theorem milnorKummerSymbol_gmul (p q : ℕ)
    (x : MilnorKTheory k p) (y : MilnorKTheory k q) :
    milnorKummerSymbol k n (p + q) (GradedMonoid.GMul.mul x y) =
      Stacks.Kummer.rootsOfUnityPowerProductHom (𝟙 (Spec (.of k))) n p q
        (milnorKummerSymbol k n p x) (milnorKummerSymbol k n q y) := by
  let L : MilnorKTheory k p →+ MilnorKTheory k q →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n (p + q) :=
    AddMonoidHom.mk' (fun a => (milnorKummerSymbol k n (p + q)).toAddMonoidHom.comp
      (nativeMilnorProductHom k p q a)) (by
      intro a b
      apply AddMonoidHom.ext
      intro c
      simp only [map_add, AddMonoidHom.comp_apply, AddMonoidHom.add_apply])
  let R : MilnorKTheory k p →+ MilnorKTheory k q →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n (p + q) :=
    AddMonoidHom.mk' (fun a =>
      (Stacks.Kummer.rootsOfUnityPowerProductHom (𝟙 (Spec (.of k))) n p q
        (milnorKummerSymbol k n p a)).comp (milnorKummerSymbol k n q).toAddMonoidHom) (by
      intro a b
      apply AddMonoidHom.ext
      intro c
      simp only [map_add, AddMonoidHom.comp_apply, AddMonoidHom.add_apply])
  have hLR : L = R := by
    apply milnorKTheory_addHom_ext
    intro a
    apply milnorKTheory_addHom_ext
    intro b
    change milnorKummerSymbol k n (p + q)
      (GradedMonoid.GMul.mul (milnorKTupleSymbol a) (milnorKTupleSymbol b)) =
        Stacks.Kummer.rootsOfUnityPowerProductHom (𝟙 (Spec (.of k))) n p q
          (milnorKummerSymbol k n p (milnorKTupleSymbol a))
          (milnorKummerSymbol k n q (milnorKTupleSymbol b))
    rw [milnorKTupleSymbol_gmul, milnorKummerSymbol_tuple,
      milnorKummerSymbol_tuple, milnorKummerSymbol_tuple]
    exact orderedFieldKummerCup_append k n p q a b
  exact DFunLike.congr_fun (DFunLike.congr_fun hLR x) y

end AlgebraicGeometry.EtaleCohomology.MilnorKummer
end
