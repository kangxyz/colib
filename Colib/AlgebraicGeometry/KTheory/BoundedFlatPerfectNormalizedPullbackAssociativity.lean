/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectNormalizedPullbackUnits

/-! # Associativity of the original chosen-zero normalized pullback

The actual two geometric triple-pullback comparison transformations agree after
conjugating by the same chosen-zero normalization used by the native prespectrum maps.

Implementation provenance: Quillen `BoundedFlat/NormalizedPullbackCoherence.lean:71-102`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NComp" => boundedAboveFlatPerfectNormalizedPullbackCompIso
local notation "B" => boundedAboveFlatPerfectPullback
local notation "BComp" => boundedAboveFlatPerfectPullbackCompIso
local notation "rebaseIso" => boundedAboveFlatPerfectPullbackNormalizationIso

/-- Move the explicit source transport through the inverse of the same rebasing isomorphism. -/
private theorem rebaseTransport_app_assoc {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (e : f = g) (A : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory)
    {Obj : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory}
    (k : (B g).obj A ⟶ Obj) :
    (eqToHom (congrArg N e)).app A ≫ (rebaseIso g).inv.app A ≫ k =
      (rebaseIso f).inv.app A ≫
        (eqToHom (congrArg B e)).app A ≫ k := by
  subst g
  simp

set_option maxHeartbeats 1200000 in
-- Conjugate the three component comparisons and match their common raw chain-map composite.
/-- Both normalized decomposition routes retain the actual associator and scheme transport. -/
theorem boundedAboveFlatPerfectNormalizedPullbackCompIso_two_routes {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (NComp f (g ≫ h)).hom ≫
      whiskerRight (NComp g h).hom (N f) ≫
      (Functor.associator (N h) (N g) (N f)).hom =
    eqToHom (congrArg N (Category.assoc f g h).symm) ≫
      (NComp (f ≫ g) h).hom ≫
      whiskerLeft (N h) (NComp f g).hom := by
  apply NatTrans.ext
  funext A
  simp only [comp_obj, boundedAboveFlatPerfectNormalizedPullbackCompIso, Iso.trans_hom,
    Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_comp,
    whiskerRight_twice, Category.assoc, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, associator_hom_app, associator_inv_app, Functor.comp_map,
    Category.comp_id, Category.id_comp, whiskerLeft_comp, whiskerLeft_twice]
  erw [rebaseTransport_app_assoc (Category.assoc f g h).symm A]
  -- Cancel the normalizations of the two middle composites.
  erw [Iso.hom_inv_id_app_assoc (rebaseIso (f ≫ g)) ((N h).obj A)]
  erw [← (rebaseIso f).hom.naturality_assoc ((rebaseIso (g ≫ h)).inv.app A)]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id (B f) ((B (g ≫ h)).obj A), Category.id_comp]
  -- Move the remaining normalizations to the same end of both raw routes.
  erw [← (rebaseIso f).hom.naturality_assoc ((BComp g h).hom.app A),
    ← (rebaseIso f).hom.naturality_assoc ((B g).map ((rebaseIso h).hom.app A))]
  let γ := (rebaseIso g).hom.app ((N h).obj A)
  let ρ := (rebaseIso f).hom.app ((N g).obj ((N h).obj A))
  have lastNaturality :
      (rebaseIso f).hom.app ((B g).obj ((N h).obj A)) ≫ (N f).map γ =
        (B f).map γ ≫ ρ :=
    ((rebaseIso f).hom.naturality γ).symm
  erw [lastNaturality]
  have rightNaturality := congrArg (fun k ↦ k ≫ (B f).map γ ≫ ρ)
    ((BComp f g).hom.naturality ((rebaseIso h).hom.app A))
  simp only [Category.assoc, Functor.comp_map] at rightNaturality
  erw [rightNaturality]
  have hc := congrArg (fun e ↦ e.app A) (boundedAboveFlatPerfectPullbackCompIso_two_routes f g h)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hc
  erw [← Category.assoc ((BComp f (g ≫ h)).hom.app A)
    ((B f).map ((BComp g h).hom.app A)), hc]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules
