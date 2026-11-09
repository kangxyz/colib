/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackCoherence

/-!
# Coherence laws for actual bounded-above-flat perfect pullback

The composition pentagon and both unit laws are reflected through the faithful underlying-chain
inclusion, degree by degree, from Mathlib's geometric sheaf-module pullback laws. The native
ringed-space perfect predicate is unchanged. Explicit component lemmas retain the equality
transports while avoiding an identification of old and native perfectness predicates.

Adapted from `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/`
`PullbackCoherence.lean` and `UnitCoherence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
universe u

namespace AlgebraicGeometry.Scheme.Modules

private lemma pullbackComp_associativity_app {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : T.Modules) :
    (pullbackComp f (g ≫ h)).inv.app M ≫
      (pullback f).map ((pullbackComp g h).inv.app M) ≫
      (pullbackComp f g).hom.app ((pullback h).obj M) ≫
      (pullbackComp (f ≫ g) h).hom.app M =
        (eqToHom (by simp) : (pullback (f ≫ g ≫ h)).obj M ⟶
          (pullback ((f ≫ g) ≫ h)).obj M) := by
  simpa using congrArg (fun η ↦ η.app M) (pseudofunctor_associativity f g h)

private lemma pullbackComp_left_unitality_app {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) :
    (pullbackComp f (𝟙 Y)).inv.app M ≫
      (pullback f).map ((pullbackId Y).hom.app M) =
        (eqToHom (by simp) : (pullback (f ≫ 𝟙 Y)).obj M ⟶ (pullback f).obj M) := by
  simpa using congrArg (fun η ↦ η.app M) (pseudofunctor_left_unitality f)

private lemma pullbackComp_right_unitality_app {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) :
    (pullbackComp (𝟙 X) f).inv.app M ≫
      (pullbackId X).hom.app ((pullback f).obj M) =
        (eqToHom (by simp) : (pullback (𝟙 X ≫ f)).obj M ⟶ (pullback f).obj M) := by
  simpa using congrArg (fun η ↦ η.app M) (pseudofunctor_right_unitality f)

private lemma eqToHom_component {X Y : Scheme.{u}}
    {F G : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory}
    (e : F = G) (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory)
    (n : ℤ) :
    ((eqToHom e).app K).hom.f n =
      eqToHom (congrArg (fun H => (H.obj K).obj.X n) e) := by
  subst e
  rfl

/-- The actual composition comparison on underlying chain maps. -/
lemma boundedAboveFlatPerfectPullbackCompIso_hom_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : (boundedAboveFlatPerfectComplex Z.toRingedSpace).FullSubcategory) :
    ((boundedAboveFlatPerfectPullbackCompIso f g).hom.app K).hom =
      (Functor.mapHomologicalComplexCompIso (pullbackComp f g)
        (ComplexShape.up ℤ)).inv.app K.obj := by
  change (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.preimage _) = _
  exact (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_preimage _

/-- The actual composition comparison on underlying chain maps. -/
lemma boundedAboveFlatPerfectPullbackCompIso_inv_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : (boundedAboveFlatPerfectComplex Z.toRingedSpace).FullSubcategory) :
    ((boundedAboveFlatPerfectPullbackCompIso f g).inv.app K).hom =
      (Functor.mapHomologicalComplexCompIso (pullbackComp f g)
        (ComplexShape.up ℤ)).hom.app K.obj := by
  change (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.preimage _) = _
  exact (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_preimage _

/-- The actual identity comparison on underlying chain maps. -/
lemma boundedAboveFlatPerfectPullbackIdIso_hom_app (X : Scheme.{u})
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :
    ((boundedAboveFlatPerfectPullbackIdIso X).hom.app K).hom =
      (NatIso.mapHomologicalComplex (pullbackId X) (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℤ)).hom.app K.obj := by
  change (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.preimage _) = _
  exact (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_preimage _

/-- The pullback functor acts on the actual underlying chain maps. -/
lemma boundedAboveFlatPerfectPullback_map_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory} (φ : K ⟶ L) :
    ((boundedAboveFlatPerfectPullback f).map φ).hom =
      ((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ.hom := rfl

/-- The original bounded-flat pullback comparisons satisfy the actual geometric associativity
loop, inherited through the faithful inclusion into complexes. -/
lemma boundedAboveFlatPerfectPullbackCompIso_associativity {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedAboveFlatPerfectPullbackCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackCompIso g h).hom
        (boundedAboveFlatPerfectPullback f) ≫
      (Functor.associator (boundedAboveFlatPerfectPullback h) (boundedAboveFlatPerfectPullback g)
        (boundedAboveFlatPerfectPullback f)).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback h)
        (boundedAboveFlatPerfectPullbackCompIso f g).inv ≫
      (boundedAboveFlatPerfectPullbackCompIso (f ≫ g) h).inv = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp]
  simp only [boundedAboveFlatPerfectPullbackCompIso_hom_app,
    boundedAboveFlatPerfectPullbackCompIso_inv_app,
    boundedAboveFlatPerfectPullback_map_hom]
  apply HomologicalComplex.hom_ext
  intro n
  rw [eqToHom_component]
  change ((pullbackComp f (g ≫ h)).inv.app (K.obj.X n) ≫
    (pullback f).map ((pullbackComp g h).inv.app (K.obj.X n))) ≫
    (pullbackComp f g).hom.app ((pullback h).obj (K.obj.X n)) ≫
    (pullbackComp (f ≫ g) h).hom.app (K.obj.X n) = _
  simp only [Category.assoc]
  convert pullbackComp_associativity_app f g h (K.obj.X n) using 1
  rfl

/-- The two original decompositions of a triple pullback agree, including the genuine functor
associator and the original scheme-composition transport. -/
lemma boundedAboveFlatPerfectPullbackCompIso_two_routes {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedAboveFlatPerfectPullbackCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackCompIso g h).hom
        (boundedAboveFlatPerfectPullback f) ≫
      (Functor.associator (boundedAboveFlatPerfectPullback h) (boundedAboveFlatPerfectPullback g)
        (boundedAboveFlatPerfectPullback f)).hom =
    eqToHom (by simp) ≫ (boundedAboveFlatPerfectPullbackCompIso (f ≫ g) h).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback h)
        (boundedAboveFlatPerfectPullbackCompIso f g).hom := by
  let e := Functor.isoWhiskerLeft (boundedAboveFlatPerfectPullback h)
    (boundedAboveFlatPerfectPullbackCompIso f g)
  apply (cancel_mono (e.inv ≫ (boundedAboveFlatPerfectPullbackCompIso (f ≫ g) h).inv)).mp
  change _ = (eqToHom (by simp) ≫ (boundedAboveFlatPerfectPullbackCompIso (f ≫ g) h).hom ≫ e.hom) ≫
    (e.inv ≫ (boundedAboveFlatPerfectPullbackCompIso (f ≫ g) h).inv)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [e, Functor.isoWhiskerLeft_inv] using
    boundedAboveFlatPerfectPullbackCompIso_associativity f g h


/-- The genuine left unit comparison on the original bounded-flat categories. -/
lemma boundedAboveFlatPerfectPullbackCompIso_left_unitality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectPullbackCompIso f (𝟙 Y)).hom ≫
      Functor.whiskerRight (boundedAboveFlatPerfectPullbackIdIso Y).hom
        (boundedAboveFlatPerfectPullback f) ≫
      (Functor.leftUnitor _).hom = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  simp only [boundedAboveFlatPerfectPullbackCompIso_hom_app,
    boundedAboveFlatPerfectPullbackIdIso_hom_app,
    boundedAboveFlatPerfectPullback_map_hom]
  apply HomologicalComplex.hom_ext
  intro n
  rw [eqToHom_component]
  change (pullbackComp f (𝟙 Y)).inv.app (K.obj.X n) ≫
    (pullback f).map ((pullbackId Y).hom.app (K.obj.X n) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.comp_id]
  convert pullbackComp_left_unitality_app f (K.obj.X n) using 1
  rfl

/-- The genuine right unit comparison on the original bounded-flat categories. -/
lemma boundedAboveFlatPerfectPullbackCompIso_right_unitality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectPullbackCompIso (𝟙 X) f).hom ≫
      Functor.whiskerLeft (boundedAboveFlatPerfectPullback f)
        (boundedAboveFlatPerfectPullbackIdIso X).hom ≫
      (Functor.rightUnitor _).hom = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  simp only [boundedAboveFlatPerfectPullbackCompIso_hom_app,
    boundedAboveFlatPerfectPullbackIdIso_hom_app]
  apply HomologicalComplex.hom_ext
  intro n
  rw [eqToHom_component]
  change (pullbackComp (𝟙 X) f).inv.app (K.obj.X n) ≫
    ((pullbackId X).hom.app ((pullback f).obj (K.obj.X n)) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.comp_id]
  convert pullbackComp_right_unitality_app f (K.obj.X n) using 1
  rfl

end AlgebraicGeometry.Scheme.Modules
