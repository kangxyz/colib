/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Whiskering

/-! Lift an identity-functor automorphism through a fully faithful functor with exact components. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v u' v'
namespace CategoryTheory.Functor.IdentityAutomorphism
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Fully faithful lifting retains the supplied identity-functor automorphism after evaluation. -/
def lift (F : C ⥤ D) [F.Full] [F.Faithful] (e : 𝟭 D ≅ 𝟭 D) : 𝟭 C ≅ 𝟭 C :=
  NatIso.ofComponents (fun x ↦ F.preimageIso (X := x) (Y := x) (e.app (F.obj x))) (fun a ↦
    F.map_injective (by simpa only [Functor.map_comp, Functor.preimageIso_hom,
      Functor.map_preimage, Functor.id_map, Functor.id_obj, Iso.app_hom] using
        e.hom.naturality (F.map a)))

/-- The forward component maps to exactly the supplied forward component. -/
theorem map_lift_hom (F : C ⥤ D) [F.Full] [F.Faithful] (e : 𝟭 D ≅ 𝟭 D) (x : C) :
    F.map ((lift F e).hom.app x) = e.hom.app (F.obj x) := by
  exact F.map_preimage (e.hom.app (F.obj x))

/-- The inverse component maps to exactly the supplied inverse component. -/
theorem map_lift_inv (F : C ⥤ D) [F.Full] [F.Faithful] (e : 𝟭 D ≅ 𝟭 D) (x : C) :
    F.map ((lift F e).inv.app x) = e.inv.app (F.obj x) := by
  exact F.map_preimage (e.inv.app (F.obj x))

/-- Apply the supplied identity automorphism pointwise to an actual functor. -/
def onFunctor (F : C ⥤ D) (e : 𝟭 D ≅ 𝟭 D) : F ≅ F :=
  NatIso.ofComponents (fun x ↦ e.app (F.obj x)) (fun a ↦ by
    simpa only [Functor.id_map, Iso.app_hom] using e.hom.naturality (F.map a))

/-- The forward component retains the supplied actual identity automorphism. -/
theorem onFunctor_hom_app (F : C ⥤ D) (e : 𝟭 D ≅ 𝟭 D) (x : C) :
    (onFunctor F e).hom.app x = e.hom.app (F.obj x) := rfl

/-- A proved component equation identifies the entire mapped component automorphism. -/
theorem mapIso_app_eq (F : C ⥤ D) (a : 𝟭 C ≅ 𝟭 C) (b : 𝟭 D ≅ 𝟭 D) (x : C)
    (h : F.map (a.hom.app x) = b.hom.app (F.obj x)) :
    F.mapIso (a.app x) = b.app (F.obj x) := by
  apply Iso.ext
  exact h

/-- The same proved component equation also identifies the mapped inverse action. -/
theorem map_inv_app_eq (F : C ⥤ D) (a : 𝟭 C ≅ 𝟭 C) (b : 𝟭 D ≅ 𝟭 D) (x : C)
    (h : F.map (a.hom.app x) = b.hom.app (F.obj x)) :
    F.map (a.inv.app x) = b.inv.app (F.obj x) :=
  congrArg Iso.inv (mapIso_app_eq F a b x h)

section
variable {E : Type*} [Category* E]

/-- Transfer exact action formulas through an equality of evaluation functors. -/
theorem whisker_hom_eq_of_evaluation (F : C ⥤ D) (P : D ⥤ E) [P.Faithful] (Q : C ⥤ E)
    (h : F ⋙ P = Q) (a : 𝟭 C ≅ 𝟭 C) (b : 𝟭 D ≅ 𝟭 D) (e : 𝟭 E ≅ 𝟭 E)
    (ha : ∀ x, Q.map (a.hom.app x) = e.hom.app (Q.obj x))
    (hb : ∀ y, P.map (b.hom.app y) = e.hom.app (P.obj y)) :
    Functor.whiskerRight a.hom F = Functor.whiskerLeft F b.hom := by
  apply NatTrans.ext
  funext x
  apply P.map_injective
  have hx : (F ⋙ P).map (a.hom.app x) =
      e.hom.app ((F ⋙ P).obj x) := by
    rw [h]
    exact ha x
  exact hx.trans (hb (F.obj x)).symm

end

end CategoryTheory.Functor.IdentityAutomorphism
