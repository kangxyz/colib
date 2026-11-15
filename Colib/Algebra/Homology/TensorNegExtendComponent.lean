/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.TensorNegExtend
/-! # Components of the original chain-to-cochain tensor comparison -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
namespace HomologicalComplex.TensorNegExtend
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{0} C]

/-- In nonpositive degree, the original full comparison is its native summand
comparison followed by the actual extension identification. -/
theorem tensorNegExtendFullIso_hom_f (K L : ChainComplex C ℕ) (n : ℕ) :
    (tensorNegExtendFullIso K L).hom.f (-(n : ℤ)) =
      tensorNegExtendInv K L n ≫
        (negExtendIso (HomologicalComplex.tensorObj K L) n).inv := by
  change (ComplexShape.embeddingDownNat.liftExtend
    (tensorNegExtendComplexIso K L).inv
    (fun _ h _ _ => h.false_of_isTruncLE.elim)).f (-(n : ℤ)) = _
  erw [ComplexShape.Embedding.liftExtend_f _ _ _ (i := n) rfl]
  simp only [restrictionXIso, eqToIso_refl, Iso.refl_inv]
  erw [Category.id_comp]
  rfl

/-- The full native comparison carries the actual `(-p,-q)` summand to `(p,q)`.
No factor is exchanged and no shift comparison is inserted. -/
theorem tensorNegExtendFullIso_hom_ι (K L : ChainComplex C ℕ)
    (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (negExtend K) (negExtend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ))
      (by omega) ≫ (tensorNegExtendFullIso K L).hom.f (-(n : ℤ)) =
    ((negExtendIso K p).hom ⊗ₘ (negExtendIso L q).hom) ≫
      ιTensorObj K L p q n h ≫
      (negExtendIso (HomologicalComplex.tensorObj K L) n).inv := by
  rw [tensorNegExtendFullIso_hom_f, ← Category.assoc,
    tensorNegExtendInv_ι K L p q n h, Category.assoc]

end HomologicalComplex.TensorNegExtend
