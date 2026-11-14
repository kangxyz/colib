/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Prespectrum.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Colimits of sequential prespectra

When suspension preserves colimits of a given shape, prespectrum colimits of
that shape are formed levelwise and each evaluation preserves them.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe w w' v u

namespace CategoryTheory.SequentialPrespectrum

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {S : C ⥤ C}
variable {J : Type w} [Category.{w'} J]
variable (F : J ⥤ SequentialPrespectrum S)
variable [HasColimitsOfShape J C] [PreservesColimitsOfShape J S]

/-- The levelwise bonding maps followed by the colimit injections form a cocone. -/
def bondingCocone (n : ℕ) : Cocone (F ⋙ evaluation n ⋙ S) where
  pt := colimit (F ⋙ evaluation (n + 1))
  ι := { app := fun j ↦ (F.obj j).bonding n ≫ colimit.ι (F ⋙ evaluation (n + 1)) j
         naturality := fun j k f ↦ by
           change S.map ((F.map f).app n) ≫ ((F.obj k).bonding n ≫
             colimit.ι (F ⋙ evaluation (n + 1)) k) =
             ((F.obj j).bonding n ≫ colimit.ι (F ⋙ evaluation (n + 1)) j) ≫ 𝟙 _
           rw [Category.comp_id, ← Category.assoc, ← (F.map f).comm n,
             Category.assoc]
           have h := colimit.w (F ⋙ evaluation (n + 1)) f
           change (F.map f).app (n + 1) ≫ colimit.ι (F ⋙ evaluation (n + 1)) k =
             colimit.ι (F ⋙ evaluation (n + 1)) j at h
           rw [h] }

/-- The prespectrum with levelwise colimits and the induced bonding maps. -/
def levelColimit : SequentialPrespectrum S where
  level n := colimit (F ⋙ evaluation n)
  bonding n := (isColimitOfPreserves S (colimit.isColimit (F ⋙ evaluation n))).desc
    (bondingCocone F n)

/-- The induced bonding map restricts to each original bonding map. -/
theorem colimitι_bonding (j : J) (n : ℕ) :
    S.map (colimit.ι (F ⋙ evaluation n) j) ≫ (levelColimit F).bonding n =
      (F.obj j).bonding n ≫ colimit.ι (F ⋙ evaluation (n + 1)) j := by
  exact (isColimitOfPreserves S (colimit.isColimit (F ⋙ evaluation n))).fac
    (bondingCocone F n) j

/-- The original levelwise colimit injections form a prespectrum cocone. -/
def levelColimitCocone : Cocone F where
  pt := levelColimit F
  ι := { app := fun j ↦ ⟨fun n ↦ colimit.ι (F ⋙ evaluation n) j,
           fun n ↦ (colimitι_bonding F j n).symm⟩
         naturality := fun j k f ↦ Hom.ext (funext fun n ↦ by
           change (F.map f).app n ≫ colimit.ι (F ⋙ evaluation n) k =
             colimit.ι (F ⋙ evaluation n) j ≫ 𝟙 _
           simpa using colimit.w (F ⋙ evaluation n) f) }

/-- The levelwise cocone satisfies the universal property of a colimit. -/
def levelColimitIsColimit : IsColimit (levelColimitCocone F) where
  desc c :=
    { app := fun n ↦ colimit.desc (F ⋙ evaluation n) ((evaluation n).mapCocone c)
      comm := fun n ↦ by
        apply (isColimitOfPreserves S (colimit.isColimit (F ⋙ evaluation n))).hom_ext
        intro j
        change S.map (colimit.ι (F ⋙ evaluation n) j) ≫
          (levelColimit F).bonding n ≫ colimit.desc _ _ =
          S.map (colimit.ι (F ⋙ evaluation n) j) ≫ S.map (colimit.desc _ _) ≫ _
        rw [← Category.assoc, colimitι_bonding, Category.assoc, ← Category.assoc
          (S.map (colimit.ι (F ⋙ evaluation n) j)), ← Functor.map_comp]
        have h₁ := colimit.ι_desc ((evaluation (n + 1)).mapCocone c) j
        have h₂ := colimit.ι_desc ((evaluation n).mapCocone c) j
        change colimit.ι (F ⋙ evaluation (n + 1)) j ≫
          colimit.desc (F ⋙ evaluation (n + 1)) ((evaluation (n + 1)).mapCocone c) =
          (c.ι.app j).app (n + 1) at h₁
        change colimit.ι (F ⋙ evaluation n) j ≫
          colimit.desc (F ⋙ evaluation n) ((evaluation n).mapCocone c) =
          (c.ι.app j).app n at h₂
        rw [h₁, h₂]
        exact (c.ι.app j).comm n }
  fac c j := Hom.ext (funext fun n ↦ colimit.ι_desc _ _)
  uniq c m h := by
    apply Hom.ext
    funext n
    change m.app n = colimit.desc (F ⋙ evaluation n) ((evaluation n).mapCocone c)
    apply colimit.hom_ext
    intro j
    rw [colimit.ι_desc]
    exact congrArg (fun f : (F.obj j ⟶ c.pt) ↦ f.app n) (h j)

instance : HasColimit F := ⟨⟨levelColimitCocone F, levelColimitIsColimit F⟩⟩

instance (n : ℕ) : PreservesColimit F (evaluation n) :=
  preservesColimit_of_preserves_colimit_cocone (levelColimitIsColimit F)
    (colimit.isColimit (F ⋙ evaluation n))

instance : HasColimitsOfShape J (SequentialPrespectrum S) where
  has_colimit := fun _ ↦ inferInstance

instance (n : ℕ) : PreservesColimitsOfShape J (evaluation (S := S) n) where
  preservesColimit := inferInstance

end CategoryTheory.SequentialPrespectrum
