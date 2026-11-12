/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.DiagramTransport
public import Colib.Util.References

/-!
Source: `Quillen/KTheory/Bass/DiagramTransportGroupNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Group-functor naturality of two-chart cokernel transport

The original transport of Bass cokernels commutes with a natural transformation
of the group-valued functors. Its square is proved by cancelling the original
Laurent quotient and using naturality on the actual Laurent identification.
This is a conditional diagram-transport statement, with independent category
and group universes; it asserts no geometric interchange or recursive exactness.
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
variable (T : D ⥤ C) (eP : P' ⋙ T ≅ T ⋙ P) (eL : L' ⋙ T ≅ T ⋙ L)
variable (hp : ∀ X, T.map (p'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ p.app (T.obj X))
  (hm : ∀ X, T.map (m'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ m.app (T.obj X))

/-- Two-chart transport preserves every natural map of the group-valued rows. -/
@[reassoc]
theorem contractionTransportIso_groupMap {F G : C ⥤ AddCommGrpCat.{w}}
    (α : F ⟶ G) (X : D) :
    (contractionMap p' m' (Functor.whiskerLeft T α)).app X ≫
      (contractionTransportIso p m p' m' T eP eL hp hm G).hom.app X =
    (contractionTransportIso p m p' m' T eP eL hp hm F).hom.app X ≫
      (contractionMap p m α).app (T.obj X) := by
  apply (cancel_epi ((contractionπ p' m' (T ⋙ F)).app X)).mp
  rw [← Category.assoc, contractionMap_π, Category.assoc,
    contractionTransportIso_π, contractionTransportIso_π_assoc, contractionMap_π]
  simpa only [Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc] using
    congrArg (fun f ↦ f ≫ (contractionπ p m G).app (T.obj X))
      (α.naturality (eL.hom.app X)).symm


attribute [colib_ref "quillen" "DiagramTransportGroupNaturality.lean:36"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  contractionTransportIso_groupMap

end KTheory.Bass.TwoChart
