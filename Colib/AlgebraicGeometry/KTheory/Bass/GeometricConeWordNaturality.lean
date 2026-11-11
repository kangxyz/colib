/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWords
public import Colib.KTheory.Bass.NormalizedStageNaturality

/-!
# Input naturality of the original cast-preserving geometric words

The complete power-object identifications intertwine the actual iterated cone
maps. Transporting ordinary naturality of the fixed insertion and accumulated
words through these identifications retains their original equality casts.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.GeometricConeFixedWords
open GeometricConeInterchange FiniteConeTopology NormalizedStageMap

private theorem map_transport_square {D : Type u} [Category.{v} D] (C : D ⥤ D)
    {X X' Y Y' : D} (hx : X = X') (hy : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : f ≫ eqToHom hy = eqToHom hx ≫ g) :
    C.map f ≫ eqToHom (congrArg C.obj hy) =
      eqToHom (congrArg C.obj hx) ≫ C.map g := by
  subst X'; subst Y'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  exact congrArg C.map h

private theorem transport_endomorphism_naturality {D : Type u} [Category.{v} D]
    {X X' Y Y' : D} (hx : X = X') (hy : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X) (b : Y ⟶ Y)
    (hf : f ≫ eqToHom hy = eqToHom hx ≫ g) (hn : f ≫ b = a ≫ f) :
    g ≫ (eqToHom hy.symm ≫ b ≫ eqToHom hy) =
      (eqToHom hx.symm ≫ a ≫ eqToHom hx) ≫ g := by
  subst X'; subst Y'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf ⊢
  simpa only [← hf] using hn

/-- The complete power-object cast intertwines the actual original finite cone maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeWordNaturality.lean:47"
  "adaptation" "Original complete equality transports and arbitrary input naturality."]
theorem power_obj_naturality (i : ℕ)
    {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    (Functor.FixedWords.power coneFunctor i).map η ≫ eqToHom (power_obj i G) =
      eqToHom (power_obj i F) ≫ iterateMap squareFunctor i η := by
  induction i with
  | zero => exact (Category.comp_id η).trans (Category.id_comp η).symm
  | succ i ih =>
    exact map_transport_square coneFunctor (power_obj i F) (power_obj i G)
      ((Functor.FixedWords.power coneFunctor i).map η) (iterateMap squareFunctor i η) ih

/-- The unchanged insertion word is natural in arbitrary actual input diagram maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeWordNaturality.lean:58"
  "adaptation" "Original complete equality transports and arbitrary input naturality."]
theorem betaAt_naturality (i : ℕ)
    {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    iterateMap squareFunctor (i + 1) η ≫ (betaAt i G).hom =
      (betaAt i F).hom ≫ iterateMap squareFunctor (i + 1) η :=
  transport_endomorphism_naturality (power_obj (i + 1) F) (power_obj (i + 1) G)
    ((Functor.FixedWords.power coneFunctor (i + 1)).map η)
    (iterateMap squareFunctor (i + 1) η) ((beta i).hom.app F) ((beta i).hom.app G)
    (power_obj_naturality (i + 1) η) ((beta i).hom.naturality η)

/-- The unchanged accumulated word is natural with its two original power casts retained. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeWordNaturality.lean:68"
  "adaptation" "Original complete equality transports and arbitrary input naturality."]
theorem wordAt_naturality (i : ℕ)
    {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    iterateMap squareFunctor i η ≫ (wordAt i G).hom =
      (wordAt i F).hom ≫ iterateMap squareFunctor i η :=
  transport_endomorphism_naturality (power_obj i F) (power_obj i G)
    ((Functor.FixedWords.power coneFunctor i).map η) (iterateMap squareFunctor i η)
    ((word i).hom.app F) ((word i).hom.app G)
    (power_obj_naturality i η) ((word i).hom.naturality η)

end KTheory.Bass.GeometricConeFixedWords
