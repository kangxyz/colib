/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.MappingCone.ShortExact
public import Colib.Algebra.Homology.MappingCone.FunctorMapIso
public import Colib.Algebra.Homology.MappingCone.MapCongr

/-! # Natural isomorphisms of signed mapping cones -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
universe u v u' v' w z

namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {D : Type w} [Category.{z} D]

/-- An actual natural isomorphism on both endpoints induces a natural isomorphism of cones. -/
def mappingConeNatTransFunctorIso {F G F' G' : D ⥤ CochainComplex A ℤ}
    (α : F ⟶ G) (β : F' ⟶ G') (i : F ≅ F') (j : G ≅ G')
    (h : α ≫ j.hom = i.hom ≫ β) :
    mappingConeNatTransFunctor α ≅ mappingConeNatTransFunctor β :=
  NatIso.ofComponents (fun K => by
    have hK : α.app K ≫ j.hom.app K = i.hom.app K ≫ β.app K :=
      NatTrans.congr_app h K
    have hK' : β.app K ≫ j.inv.app K = i.inv.app K ≫ α.app K := by
      rw [← cancel_epi (i.hom.app K), Iso.hom_inv_id_app_assoc,
        ← reassoc_of% hK, Iso.hom_inv_id_app, Category.comp_id]
    change mappingCone (α.app K) ≅ mappingCone (β.app K)
    exact {
      hom := mappingCone.map _ _ (i.hom.app K) (j.hom.app K) hK
      inv := mappingCone.map _ _ (i.inv.app K) (j.inv.app K) hK'
      hom_inv_id := by
        rw [← mappingCone.map_comp, ← mappingCone.map_id (α.app K)]
        exact mappingCone.map_congr_endpoints _ _ _ _ (by simp) (by simp)
      inv_hom_id := by
        rw [← mappingCone.map_comp, ← mappingCone.map_id (β.app K)]
        exact mappingCone.map_congr_endpoints _ _ _ _ (by simp) (by simp) }) (fun f => by
    dsimp [mappingConeNatTransFunctor]
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    exact mappingCone.map_congr_endpoints _ _ _ _ (i.hom.naturality f) (j.hom.naturality f))

end CochainComplex
