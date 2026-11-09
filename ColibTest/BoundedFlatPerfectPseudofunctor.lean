/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPseudofunctor

/-! Public consumer of the actual pullback constraints on arbitrary schemes and rings. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

example {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedAboveFlatPerfectPullbackCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackCompIso g h).hom
        (boundedAboveFlatPerfectPullback f) ≫
      (Functor.associator (boundedAboveFlatPerfectPullback h) (boundedAboveFlatPerfectPullback g)
        (boundedAboveFlatPerfectPullback f)).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback h)
        (boundedAboveFlatPerfectPullbackCompIso f g).inv ≫
      (boundedAboveFlatPerfectPullbackCompIso (f ≫ g) h).inv = eqToHom (by simp) :=
  boundedAboveFlatPerfectPullbackCompIso_associativity f g h

example {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedAboveFlatPerfectPullbackCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackCompIso g h).hom
        (boundedAboveFlatPerfectPullback f) ≫
      (Functor.associator (boundedAboveFlatPerfectPullback h) (boundedAboveFlatPerfectPullback g)
        (boundedAboveFlatPerfectPullback f)).hom =
    eqToHom (by simp) ≫ (boundedAboveFlatPerfectPullbackCompIso (f ≫ g) h).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback h)
        (boundedAboveFlatPerfectPullbackCompIso f g).hom :=
  boundedAboveFlatPerfectPullbackCompIso_two_routes f g h

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectPullbackCompIso f (𝟙 Y)).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackIdIso Y).hom
        (boundedAboveFlatPerfectPullback f) ≫
      (Functor.leftUnitor _).hom = eqToHom (by simp) :=
  boundedAboveFlatPerfectPullbackCompIso_left_unitality f

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectPullbackCompIso (𝟙 X) f).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback f)
        (boundedAboveFlatPerfectPullbackIdIso X).hom ≫
      (Functor.rightUnitor _).hom = eqToHom (by simp) :=
  boundedAboveFlatPerfectPullbackCompIso_right_unitality f

example (R : CommRingCat.{u}) :
    boundedAboveFlatAffinePseudofunctor.obj ⟨R⟩ =
      ↧((boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :=
  boundedAboveFlatAffinePseudofunctor_obj R

example {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffinePseudofunctor.map f.toLoc).toFunctor =
      boundedAboveFlatPerfectPullback (Spec.map f) :=
  boundedAboveFlatAffinePseudofunctor_map f

example {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffinePseudofunctor.mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≫
        (boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)).hom :=
  boundedAboveFlatAffinePseudofunctor_mapComp_hom f g

example (R : CommRingCat.{u}) :
    (boundedAboveFlatAffinePseudofunctor.mapId ⟨R⟩).hom.toNatTrans =
      eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_id R)) ≫
        (boundedAboveFlatPerfectPullbackIdIso (Spec R)).hom :=
  boundedAboveFlatAffinePseudofunctor_mapId_hom R

-- An inhabited, concrete identity specialization, not a terminal-category substitute.
example :
    (boundedAboveFlatAffinePseudofunctor.map (𝟙 (CommRingCat.of ℤ)).toLoc).toFunctor =
      boundedAboveFlatPerfectPullback (Spec.map (𝟙 (CommRingCat.of ℤ))) :=
  boundedAboveFlatAffinePseudofunctor_map _

example :
    (boundedAboveFlatAffinePseudofunctor.mapId ⟨CommRingCat.of ℤ⟩).hom.toNatTrans =
      eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_id (CommRingCat.of ℤ))) ≫
        (boundedAboveFlatPerfectPullbackIdIso (Spec (CommRingCat.of ℤ))).hom :=
  boundedAboveFlatAffinePseudofunctor_mapId_hom _

example {R S T U : CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ U) :
    (boundedAboveFlatPerfectPullbackCompIso (Spec.map c) ((Spec.map b) ≫ (Spec.map a))).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackCompIso (Spec.map b) (Spec.map a)).hom
        (boundedAboveFlatPerfectPullback (Spec.map c)) ≫
      (Functor.associator (boundedAboveFlatPerfectPullback (Spec.map a))
        (boundedAboveFlatPerfectPullback (Spec.map b))
        (boundedAboveFlatPerfectPullback (Spec.map c))).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback (Spec.map a))
        (boundedAboveFlatPerfectPullbackCompIso (Spec.map c) (Spec.map b)).inv ≫
      (boundedAboveFlatPerfectPullbackCompIso
        ((Spec.map c) ≫ (Spec.map b)) (Spec.map a)).inv = eqToHom (by simp) :=
  boundedAboveFlatPerfectPullbackCompIso_associativity (Spec.map c) (Spec.map b) (Spec.map a)

example {R S T U : CommRingCat.{u}} (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ U) :
    (boundedAboveFlatPerfectPullbackCompIso (Spec.map c) ((Spec.map b) ≫ (Spec.map a))).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackCompIso (Spec.map b) (Spec.map a)).hom
        (boundedAboveFlatPerfectPullback (Spec.map c)) ≫
      (Functor.associator (boundedAboveFlatPerfectPullback (Spec.map a))
        (boundedAboveFlatPerfectPullback (Spec.map b))
        (boundedAboveFlatPerfectPullback (Spec.map c))).hom =
    eqToHom (by simp) ≫ (boundedAboveFlatPerfectPullbackCompIso
      ((Spec.map c) ≫ (Spec.map b)) (Spec.map a)).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback (Spec.map a))
        (boundedAboveFlatPerfectPullbackCompIso (Spec.map c) (Spec.map b)).hom :=
  boundedAboveFlatPerfectPullbackCompIso_two_routes (Spec.map c) (Spec.map b) (Spec.map a)

example {R S : CommRingCat.{u}} (a : R ⟶ S) :
    (boundedAboveFlatPerfectPullbackCompIso (Spec.map a) (𝟙 (Spec R))).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackIdIso (Spec R)).hom
        (boundedAboveFlatPerfectPullback (Spec.map a)) ≫
      (Functor.leftUnitor _).hom = eqToHom (by simp) :=
  boundedAboveFlatPerfectPullbackCompIso_left_unitality (Spec.map a)

example {R S : CommRingCat.{u}} (a : R ⟶ S) :
    (boundedAboveFlatPerfectPullbackCompIso (𝟙 (Spec S)) (Spec.map a)).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback (Spec.map a))
        (boundedAboveFlatPerfectPullbackIdIso (Spec S)).hom ≫
      (Functor.rightUnitor _).hom = eqToHom (by simp) :=
  boundedAboveFlatPerfectPullbackCompIso_right_unitality (Spec.map a)

example (X : Scheme.{u}) :
    boundedAboveFlatPerfectPseudofunctor.obj ⟨Opposite.op X⟩ =
      ↧((boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :=
  boundedAboveFlatPerfectPseudofunctor_obj X

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectPseudofunctor.map f.op.toLoc).toFunctor =
      boundedAboveFlatPerfectPullback f :=
  boundedAboveFlatPerfectPseudofunctor_map f

example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedAboveFlatPerfectPseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans =
      (boundedAboveFlatPerfectPullbackCompIso f g).hom :=
  boundedAboveFlatPerfectPseudofunctor_mapComp_hom f g

example (X : Scheme.{u}) :
    (boundedAboveFlatPerfectPseudofunctor.mapId ⟨Opposite.op X⟩).hom.toNatTrans =
      (boundedAboveFlatPerfectPullbackIdIso X).hom :=
  boundedAboveFlatPerfectPseudofunctor_mapId_hom X

-- Concrete nonidentity composable coefficient maps: diagonal followed by first projection.
private def diagonal : CommRingCat.of ℤ ⟶ CommRingCat.of (ℤ × ℤ) :=
  CommRingCat.ofHom ((RingHom.id ℤ).prod (RingHom.id ℤ))

private def firstProjection : CommRingCat.of (ℤ × ℤ) ⟶ CommRingCat.of ℤ :=
  CommRingCat.ofHom (RingHom.fst ℤ ℤ)

example :
    (boundedAboveFlatAffinePseudofunctor.mapComp diagonal.toLoc
      firstProjection.toLoc).hom.toNatTrans =
      eqToHom (congrArg boundedAboveFlatPerfectPullback
        (Spec.map_comp diagonal firstProjection)) ≫
        (boundedAboveFlatPerfectPullbackCompIso
          (Spec.map firstProjection) (Spec.map diagonal)).hom :=
  boundedAboveFlatAffinePseudofunctor_mapComp_hom diagonal firstProjection

example : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1} :=
  boundedAboveFlatPerfectPseudofunctor

example : Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} :=
  boundedAboveFlatAffinePseudofunctor

open CategoryTheory.Bicategory

-- The actual affine constraint itself satisfies the pentagon and units, not only its
-- underlying geometric comparisons. The Spec transports above are retained in these maps.
example {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    let F : Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} :=
      boundedAboveFlatAffinePseudofunctor.{u}
    F.map₂ (α_ f.toLoc g.toLoc h.toLoc).hom =
      (F.mapComp (f.toLoc ≫ g.toLoc) h.toLoc).hom ≫
        (F.mapComp f.toLoc g.toLoc).hom ▷ F.map h.toLoc ≫
        (α_ (F.map f.toLoc) (F.map g.toLoc) (F.map h.toLoc)).hom ≫
        F.map f.toLoc ◁ (F.mapComp g.toLoc h.toLoc).inv ≫
        (F.mapComp f.toLoc (g.toLoc ≫ h.toLoc)).inv :=
  boundedAboveFlatAffinePseudofunctor.map₂_associator f.toLoc g.toLoc h.toLoc

example {R S : CommRingCat.{u}} (f : R ⟶ S) :
    let F : Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} :=
      boundedAboveFlatAffinePseudofunctor.{u}
    F.map₂ (λ_ f.toLoc).hom =
      (F.mapComp (𝟙 R).toLoc f.toLoc).hom ≫
        (F.mapId (LocallyDiscrete.mk R)).hom ▷ F.map f.toLoc ≫
        (λ_ (F.map f.toLoc)).hom :=
  boundedAboveFlatAffinePseudofunctor.map₂_left_unitor f.toLoc

example {R S : CommRingCat.{u}} (f : R ⟶ S) :
    let F : Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} :=
      boundedAboveFlatAffinePseudofunctor.{u}
    F.map₂ (ρ_ f.toLoc).hom =
      (F.mapComp f.toLoc (𝟙 S).toLoc).hom ≫
        F.map f.toLoc ◁ (F.mapId (LocallyDiscrete.mk S)).hom ≫
        (ρ_ (F.map f.toLoc)).hom :=
  boundedAboveFlatAffinePseudofunctor.map₂_right_unitor f.toLoc

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :
    ((boundedAboveFlatPerfectPullback f).obj K).obj =
      ((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj := rfl

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory} (φ : K ⟶ L) :
    ((boundedAboveFlatPerfectPullback f).map φ).hom =
      ((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom :=
  boundedAboveFlatPerfectPullback_map_hom f φ

example {R S : CommRingCat.{u}} (f : R ⟶ S)
    (K : (boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) :
    (((boundedAboveFlatAffinePseudofunctor.map f.toLoc).toFunctor).obj K).obj =
      ((pullback (Spec.map f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj := rfl
