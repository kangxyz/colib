/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# A left-adjoint comparison is monoidal from the second unit

The second left adjoint need only be lax monoidal. In particular, to compare a
strong monoidal inverse image with canonical lax monoidal restriction, it suffices
to verify the restriction adjunction's unit on sections. No strong structure on
restriction, and no assumed monoidality of the comparison, is required.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory

namespace Colib.MonoidalAdjunction

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  {L H : C ⥤ D} {R : D ⥤ C}
  [L.Monoidal] [H.LaxMonoidal] [R.LaxMonoidal]
  (adjL : L ⊣ R) (adjH : H ⊣ R)
  [adjL.IsMonoidal] [NatTrans.IsMonoidal adjH.unit]

/-- The mate of the second unit, expressed by unitors, whiskering and the first counit. -/
def unitMate : L ⟶ H :=
  (Functor.leftUnitor L).inv ≫
    Functor.whiskerRight adjH.unit L ≫
    (Functor.associator H R L).hom ≫
    Functor.whiskerLeft H adjL.counit ≫
    (Functor.rightUnitor H).hom

/-- All pieces of the unit mate are monoidal natural transformations. -/
instance unitMate_isMonoidal : NatTrans.IsMonoidal (unitMate adjL adjH) := by
  unfold unitMate
  infer_instance

omit [MonoidalCategory C] [MonoidalCategory D] [L.Monoidal] [H.LaxMonoidal]
  [R.LaxMonoidal] [adjL.IsMonoidal] [NatTrans.IsMonoidal adjH.unit] in
/-- The mate of the second unit is the canonical comparison of left adjoints. -/
theorem unitMate_eq_leftAdjointUniq :
    unitMate adjL adjH = (Adjunction.leftAdjointUniq adjL adjH).hom := by
  ext X
  have h := congrArg (adjL.homEquiv X (H.obj X)).symm
    (Adjunction.homEquiv_leftAdjointUniq_hom_app adjL adjH X)
  simpa [unitMate, Adjunction.homEquiv_counit] using h.symm

/-- A monoidal first adjunction and a monoidal second unit make the actual canonical
left-adjoint comparison monoidal, even when the second left adjoint is only lax. -/
theorem leftAdjointUniq_isMonoidal_of_unit :
    NatTrans.IsMonoidal (Adjunction.leftAdjointUniq adjL adjH).hom := by
  rw [← unitMate_eq_leftAdjointUniq adjL adjH]
  infer_instance

/-- The tensor compatibility square for the canonical comparison, without assuming it. -/
theorem leftAdjointUniq_tensor_of_unit (A B : C) :
    ((Adjunction.leftAdjointUniq adjL adjH).hom.app A ⊗ₘ
        (Adjunction.leftAdjointUniq adjL adjH).hom.app B) ≫
        Functor.LaxMonoidal.μ H A B =
      Functor.LaxMonoidal.μ L A B ≫
        (Adjunction.leftAdjointUniq adjL adjH).hom.app (A ⊗ B) := by
  have := leftAdjointUniq_isMonoidal_of_unit adjL adjH
  exact (NatTrans.IsMonoidal.tensor (τ := (Adjunction.leftAdjointUniq adjL adjH).hom) A B).symm

end Colib.MonoidalAdjunction
