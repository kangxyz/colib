/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.FiniteEtaleTrace

/-!
# Coefficient naturality of the native finite étale trace

The actual trace is a sum of restrictions over a split étale neighborhood. Every morphism
of abelian sheaves commutes with this sum. Cover density then gives coefficient naturality
of the global trace. This is independent of a choice of splitting and supplies an input to
Kummer boundary compatibility; it does not assert that compatibility itself.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
attribute [local instance] Stacks.Etale.IsSplitOver.finite_I
variable {S Y : Scheme.{u}} (g : Y ⟶ S) [Etale g]
  {G H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : G ⟶ H)

/-- A morphism of coefficients commutes with the split trace. -/
theorem splitTrace_naturality (U : S.Etale) (h : Stacks.Etale.IsSplitOver g U.hom) :
    φ.hom.app (op (baseChangeCompose g U)) ≫ splitTrace g H U h rfl =
      splitTrace g G U h rfl ≫ φ.hom.app (op U) := by
  let : Fintype h.I := Fintype.ofFinite _
  ext x
  simp only [ConcreteCategory.comp_apply, splitTrace_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ConcreteCategory.congr_hom (φ.hom.naturality (sheetSection g U h rfl i).op).symm x

variable [IsFinite g]

/-- The finite étale trace is natural in its abelian-sheaf coefficient. -/
theorem finiteEtaleTrace_naturality :
    (etaleAbelianDirectImage.{u, 0} g).map ((etaleRestriction.{u, 0} g).map φ) ≫
      finiteEtaleTrace g H = finiteEtaleTrace g G ≫ φ := by
  apply Sheaf.hom_ext
  apply (Functor.IsCoverDense.restrictHomEquivHom
    (G := ObjectProperty.ι (IsSplitObject g))).symm.injective
  apply NatTrans.ext
  funext U
  change φ.hom.app (op (baseChangeCompose g U.unop.obj)) ≫
    (finiteEtaleTrace g H).hom.app (op U.unop.obj) =
      (finiteEtaleTrace g G).hom.app (op U.unop.obj) ≫ φ.hom.app (op U.unop.obj)
  rw [finiteEtaleTrace_app g H U.unop.obj U.unop.property.some,
    finiteEtaleTrace_app g G U.unop.obj U.unop.property.some]
  exact splitTrace_naturality g φ U.unop.obj U.unop.property.some

end Stacks.EtaleCohomology
end
