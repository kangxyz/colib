/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Prespectrum.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Limits of sequential prespectra

Limits are formed levelwise, without a preservation hypothesis on suspension.
The bonding map is induced by the suspended projections and the original
bonding maps.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe w w' v u

namespace CategoryTheory.SequentialPrespectrum

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {S : C ⥤ C}
variable {J : Type w} [Category.{w'} J]
variable (F : J ⥤ SequentialPrespectrum S) [HasLimitsOfShape J C]

/-- The suspended limit projections followed by bonding maps form a cone. -/
def bondingLimitCone (n : ℕ) : Cone (F ⋙ evaluation (n + 1)) where
  pt := S.obj (limit (F ⋙ evaluation n))
  π := { app := fun j ↦ S.map (limit.π (F ⋙ evaluation n) j) ≫ (F.obj j).bonding n
         naturality := fun j k f ↦ by
           symm
           change (S.map (limit.π (F ⋙ evaluation n) j) ≫ (F.obj j).bonding n) ≫
             (F.map f).app (n + 1) = 𝟙 _ ≫
               (S.map (limit.π (F ⋙ evaluation n) k) ≫ (F.obj k).bonding n)
           rw [Category.id_comp, Category.assoc, (F.map f).comm, ← Category.assoc,
             ← Functor.map_comp]
           have h := limit.w (F ⋙ evaluation n) f
           change limit.π (F ⋙ evaluation n) j ≫ (F.map f).app n =
             limit.π (F ⋙ evaluation n) k at h
           rw [h] }

/-- The prespectrum with levelwise limits and the induced bonding maps. -/
def levelLimit : SequentialPrespectrum S where
  level n := limit (F ⋙ evaluation n)
  bonding n := limit.lift _ (bondingLimitCone F n)

/-- The induced bonding map commutes with each limit projection. -/
theorem bonding_limitπ (j : J) (n : ℕ) :
    (levelLimit F).bonding n ≫ limit.π (F ⋙ evaluation (n + 1)) j =
      S.map (limit.π (F ⋙ evaluation n) j) ≫ (F.obj j).bonding n :=
  limit.lift_π _ _

/-- The levelwise limit projections form a prespectrum cone. -/
def levelLimitCone : Cone F where
  pt := levelLimit F
  π := { app := fun j ↦ ⟨fun n ↦ limit.π (F ⋙ evaluation n) j,
           fun n ↦ bonding_limitπ F j n⟩
         naturality := fun j k f ↦ Hom.ext (funext fun n ↦ by
           symm
           change (limit.π (F ⋙ evaluation n) j ≫ (F.map f).app n) =
             𝟙 _ ≫ limit.π (F ⋙ evaluation n) k
           simpa using limit.w (F ⋙ evaluation n) f) }

/-- The levelwise cone satisfies the universal property of a limit. -/
def levelLimitIsLimit : IsLimit (levelLimitCone F) where
  lift c :=
    { app := fun n ↦ limit.lift (F ⋙ evaluation n) ((evaluation n).mapCone c)
      comm := fun n ↦ by
        apply limit.hom_ext
        intro j
        change (c.pt.bonding n ≫ limit.lift (F ⋙ evaluation (n + 1))
          ((evaluation (n + 1)).mapCone c)) ≫ limit.π (F ⋙ evaluation (n + 1)) j =
          (S.map (limit.lift (F ⋙ evaluation n) ((evaluation n).mapCone c)) ≫
            (levelLimit F).bonding n) ≫ limit.π (F ⋙ evaluation (n + 1)) j
        rw [Category.assoc, limit.lift_π, Category.assoc, bonding_limitπ, ← Category.assoc,
          ← Functor.map_comp, limit.lift_π]
        exact (c.π.app j).comm n }
  fac c j := Hom.ext (funext fun n ↦ limit.lift_π _ _)
  uniq c m h := by
    apply Hom.ext
    funext n
    change m.app n = limit.lift (F ⋙ evaluation n) ((evaluation n).mapCone c)
    apply limit.hom_ext
    intro j
    rw [limit.lift_π]
    exact congrArg (fun f : (c.pt ⟶ F.obj j) ↦ f.app n) (h j)

instance : HasLimit F := ⟨⟨levelLimitCone F, levelLimitIsLimit F⟩⟩

instance (n : ℕ) : PreservesLimit F (evaluation n) :=
  preservesLimit_of_preserves_limit_cone (levelLimitIsLimit F)
    (limit.isLimit (F ⋙ evaluation n))

instance : HasLimitsOfShape J (SequentialPrespectrum S) where
  has_limit := fun _ ↦ inferInstance

instance (n : ℕ) : PreservesLimitsOfShape J (evaluation (S := S) n) where
  preservesLimit := inferInstance

/-- All limits of the specified size are formed levelwise. -/
instance [HasLimitsOfSize.{w', w} C] : HasLimitsOfSize.{w', w} (SequentialPrespectrum S) where
  has_limits_of_shape := fun _ ↦ inferInstance

end CategoryTheory.SequentialPrespectrum
