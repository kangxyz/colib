/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso

/-!
# Sequential prespectra for an endofunctor

A prespectrum for a specified suspension functor has levels indexed by
the natural numbers and a bonding map from each suspended level to its
successor. A comparison of suspension functors transports the actual
bonding maps along a functor.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A sequence of objects with bonding maps for the specified suspension. -/
structure SequentialPrespectrum (S : C ⥤ C) where
  /-- The object in each degree. -/
  level : ℕ → C
  /-- The bonding map out of the suspended level. -/
  bonding (n : ℕ) : S.obj (level n) ⟶ level (n + 1)

namespace SequentialPrespectrum

variable {S : C ⥤ C}

/-- A levelwise map compatible with the bonding maps. -/
@[ext]
structure Hom (X Y : SequentialPrespectrum S) where
  /-- The map in each degree. -/
  app (n : ℕ) : X.level n ⟶ Y.level n
  /-- Compatibility with the original bonding maps. -/
  comm (n : ℕ) : X.bonding n ≫ app (n + 1) = S.map (app n) ≫ Y.bonding n

instance : Category.{v} (SequentialPrespectrum S) where
  Hom := Hom
  id X := ⟨fun n ↦ 𝟙 (X.level n), fun n ↦ by simp⟩
  comp f g := ⟨fun n ↦ f.app n ≫ g.app n, fun n ↦ by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, Functor.map_comp, Category.assoc]⟩
  id_comp f := Hom.ext (funext fun n ↦ Category.id_comp (f.app n))
  comp_id f := Hom.ext (funext fun n ↦ Category.comp_id (f.app n))
  assoc f g h := Hom.ext (funext fun n ↦ Category.assoc (f.app n) (g.app n) (h.app n))

/-- Evaluation at a degree retains the actual level and level map. -/
@[simps]
def evaluation (n : ℕ) : SequentialPrespectrum S ⥤ C where
  obj X := X.level n
  map f := f.app n

variable {D : Type u'} [Category.{v'} D] {T : D ⥤ D}

/-- Transport a prespectrum through a functor with a specified suspension comparison. -/
@[simps]
def mapFunctor (F : C ⥤ D) (α : F ⋙ T ≅ S ⋙ F) :
    SequentialPrespectrum S ⥤ SequentialPrespectrum T where
  obj X :=
    { level := fun n ↦ F.obj (X.level n)
      bonding := fun n ↦ α.hom.app (X.level n) ≫ F.map (X.bonding n) }
  map {X Y} f :=
    { app := fun n ↦ F.map (f.app n)
      comm := fun n ↦ by
        have hα : T.map (F.map (f.app n)) ≫ α.hom.app (Y.level n) =
            α.hom.app (X.level n) ≫ F.map (S.map (f.app n)) :=
          α.hom.naturality (f.app n)
        rw [Category.assoc, ← F.map_comp, f.comm, F.map_comp, ← Category.assoc, ← hα,
          Category.assoc] }
  map_id X := Hom.ext (funext fun n ↦ F.map_id (X.level n))
  map_comp f g := Hom.ext (funext fun n ↦ F.map_comp (f.app n) (g.app n))

end SequentialPrespectrum

end CategoryTheory
