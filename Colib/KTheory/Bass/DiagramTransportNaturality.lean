/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.DiagramTransport

/-!
Source: `Quillen/KTheory/Bass/DiagramTransportNaturality.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Naturality of the original two-chart cokernel transport

Two genuine transports commute with a transformation of their indexing functors
whenever their Laurent isomorphisms commute with its original Laurent action.
The proof cancels the actual epimorphic cokernel projection.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u₁ u₂ v₁ v₂ w
namespace KTheory.Bass.TwoChart
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {P L : C ⥤ C} {P' L' : D ⥤ D} (p m : P ⟶ L) (p' m' : P' ⟶ L')
variable (T U : D ⥤ C) (eP : P' ⋙ T ≅ T ⋙ P) (eL : L' ⋙ T ≅ T ⋙ L)
  (dP : P' ⋙ U ≅ U ⋙ P) (dL : L' ⋙ U ≅ U ⋙ L)
variable (hp : ∀ X, T.map (p'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ p.app (T.obj X))
  (hm : ∀ X, T.map (m'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ m.app (T.obj X))
  (kp : ∀ X, U.map (p'.app X) ≫ dL.hom.app X = dP.hom.app X ≫ p.app (U.obj X))
  (km : ∀ X, U.map (m'.app X) ≫ dL.hom.app X = dP.hom.app X ≫ m.app (U.obj X))
variable (α : T ⟶ U)
  (hL : ∀ X, α.app (L'.obj X) ≫ dL.hom.app X = eL.hom.app X ≫ L.map (α.app X))

include hL in
/-- The actual cokernel transports retain a transformation of their native Laurent rows. -/
@[reassoc]
theorem contractionTransportIso_map (F : C ⥤ AddCommGrpCat.{w}) (X : D) :
    (contractionMap p' m' (Functor.whiskerRight α F)).app X ≫
      (contractionTransportIso p m p' m' U dP dL kp km F).hom.app X =
    (contractionTransportIso p m p' m' T eP eL hp hm F).hom.app X ≫
      (contraction p m F).map (α.app X) := by
  apply (cancel_epi ((contractionπ p' m' (T ⋙ F)).app X)).mp
  rw [← Category.assoc, contractionMap_π, Category.assoc,
    contractionTransportIso_π, contractionTransportIso_π_assoc]
  rw [← (contractionπ p m F).naturality (α.app X)]
  simp only [Functor.whiskerRight_app, Functor.comp_map, ← Category.assoc, ← F.map_comp]
  exact congrArg (fun g ↦ F.map g ≫ (contractionπ p m F).app (U.obj X)) (hL X)

end KTheory.Bass.TwoChart
