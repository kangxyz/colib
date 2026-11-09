/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackLaws
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Geometric and affine bounded-above-flat pullback pseudofunctors

The objects are the native full subcategories defined by `IsPerfectComplex`, a strict upper
term bound and termwise sheaf flatness. There is no lower bound or flatness assumption on
scheme morphisms. The geometric functor is contravariant in schemes; its restriction along
`Spec.rightOp` is covariant in coefficient rings. No strictification is asserted.

Adapted from Quillen's `BoundedFlat/Pseudofunctor.lean` and `PseudofunctorCoherence.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The old locally-perfect predicate is not used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open scoped CategoryTheory.Bicategory
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual bounded-flat geometric pseudofunctor, before any strictification or normalization. -/
@[colib_tag "COL-0352",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Pseudofunctor.lean:22-36"
    "adaptation" "Actual native bounded-above-flat pullback with proved pentagon and units"]
def boundedAboveFlatPerfectPseudofunctor : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X => ↧((boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory))
    (fun f => (boundedAboveFlatPerfectPullback f.unop).toCatHom)
    (fun X => Cat.Hom.isoMk (boundedAboveFlatPerfectPullbackIdIso X.unop))
    (fun f g => Cat.Hom.isoMk (boundedAboveFlatPerfectPullbackCompIso g.unop f.unop)) ?_ ?_ ?_
  · intro W X Y Z f g h
    ext1
    exact boundedAboveFlatPerfectPullbackCompIso_associativity h.unop g.unop f.unop
  · intro X Y f
    ext1
    exact boundedAboveFlatPerfectPullbackCompIso_left_unitality f.unop
  · intro X Y f
    ext1
    exact boundedAboveFlatPerfectPullbackCompIso_right_unitality f.unop

/-- The geometric object is the unchanged native full subcategory. -/
theorem boundedAboveFlatPerfectPseudofunctor_obj (X : Scheme.{u}) :
    boundedAboveFlatPerfectPseudofunctor.obj ⟨Opposite.op X⟩ =
      ↧((boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) := rfl

/-- The geometric arrow acts by the actual termwise pullback on complexes and chain maps. -/
theorem boundedAboveFlatPerfectPseudofunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectPseudofunctor.map f.op.toLoc).toFunctor =
      boundedAboveFlatPerfectPullback f := rfl

/-- The geometric composition constraint is the original comparison, without replacement. -/
theorem boundedAboveFlatPerfectPseudofunctor_mapComp_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedAboveFlatPerfectPseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans =
      (boundedAboveFlatPerfectPullbackCompIso f g).hom := rfl

/-- The geometric identity constraint is the original identity comparison. -/
theorem boundedAboveFlatPerfectPseudofunctor_mapId_hom (X : Scheme.{u}) :
    (boundedAboveFlatPerfectPseudofunctor.mapId ⟨Opposite.op X⟩).hom.toNatTrans =
      (boundedAboveFlatPerfectPullbackIdIso X).hom := rfl

/-- Affine coefficient change uses the original `Spec` functor and actual geometric pullbacks. -/
@[colib_tag "COL-0352",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Pseudofunctor.lean:39-49"
    "adaptation" "Actual affine coefficient restriction along the native Spec functor"]
def boundedAboveFlatAffinePseudofunctor : Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat :=
  Scheme.Spec.rightOp.toPseudofunctor.comp boundedAboveFlatPerfectPseudofunctor

/-- The affine pseudofunctor retains the original bounded-flat category. -/
theorem boundedAboveFlatAffinePseudofunctor_obj (R : CommRingCat.{u}) :
    boundedAboveFlatAffinePseudofunctor.obj ⟨R⟩ =
      ↧((boundedAboveFlatPerfectComplex (Spec R).toRingedSpace).FullSubcategory) := rfl

/-- Every coefficient arrow is the actual original bounded-flat pullback functor. -/
theorem boundedAboveFlatAffinePseudofunctor_map {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffinePseudofunctor.map f.toLoc).toFunctor =
      boundedAboveFlatPerfectPullback (Spec.map f) := rfl

private lemma comp_mapComp_hom {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete D) Cat.{u, u + 1})
    {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    ((G.toPseudofunctor.comp F).mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg (fun h => (F.map h.toLoc).toFunctor) (G.map_comp f g)) ≫
        (F.mapComp (G.map f).toLoc (G.map g).toLoc).hom.toNatTrans := by
  change (F.map₂ (eqToHom (congrArg (fun h => h.toLoc) (G.map_comp f g)))).toNatTrans ≫
    (F.mapComp (G.map f).toLoc (G.map g).toLoc).hom.toNatTrans = _
  rw [PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans]

private lemma comp_mapId_hom {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (F : Pseudofunctor (LocallyDiscrete D) Cat.{u, u + 1}) (R : C) :
    ((G.toPseudofunctor.comp F).mapId ⟨R⟩).hom.toNatTrans =
      eqToHom (congrArg (fun h => (F.map h.toLoc).toFunctor) (G.map_id R)) ≫
        (F.mapId ⟨G.obj R⟩).hom.toNatTrans := by
  change (F.map₂ (eqToHom (congrArg (fun h => h.toLoc) (G.map_id R)))).toNatTrans ≫
    (F.mapId ⟨G.obj R⟩).hom.toNatTrans = _
  rw [PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans]

/-- The affine constraint is the original geometric comparison after actual `Spec` transport. -/
theorem boundedAboveFlatAffinePseudofunctor_mapComp_hom {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffinePseudofunctor.mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≫
        (boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)).hom := by
  convert comp_mapComp_hom Scheme.Spec.rightOp boundedAboveFlatPerfectPseudofunctor f g
    using 1
  rfl

/-- The affine unit is the original geometric identity comparison after actual `Spec` transport. -/
theorem boundedAboveFlatAffinePseudofunctor_mapId_hom (R : CommRingCat.{u}) :
    (boundedAboveFlatAffinePseudofunctor.mapId ⟨R⟩).hom.toNatTrans =
      eqToHom (congrArg boundedAboveFlatPerfectPullback (Spec.map_id R)) ≫
        (boundedAboveFlatPerfectPullbackIdIso (Spec R)).hom := by
  convert comp_mapId_hom Scheme.Spec.rightOp boundedAboveFlatPerfectPseudofunctor R
    using 1
  rfl


end AlgebraicGeometry.Scheme.Modules
