/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Sheafification and continuous reindexing

Reindex the canonical sheafification unit along a continuous functor, then
extend it by the sheafification adjunction. The resulting comparison also
applies degreewise to maps of homological complexes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]
variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [F.IsContinuous J K] (A : Type*) [Category* A]

local notation "R" => Functor.obj (whiskeringLeft Cᵒᵖ Dᵒᵖ A) (Functor.op F)
local notation "S" => sheafPushforwardContinuous F A J K

section

variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The reindexed sheafification unit extends to the sheafification of the
reindexed presheaf. -/
def sheafifyReindexComparison : R ⋙ presheafToSheaf J A ⟶ presheafToSheaf K A ⋙ S where
  app P := ⟨sheafifyLift J ((R).map (toSheafify K P))
    ((S).obj ((presheafToSheaf K A).obj P)).property⟩
  naturality P Q η := by
    apply ObjectProperty.hom_ext
    apply sheafify_hom_ext J _ _ ((S).obj ((presheafToSheaf K A).obj Q)).property
    change toSheafify J ((R).obj P) ≫
        (sheafifyMap J ((R).map η) ≫ sheafifyLift J ((R).map (toSheafify K Q)) _) =
      toSheafify J ((R).obj P) ≫
        (sheafifyLift J ((R).map (toSheafify K P)) _ ≫ (R).map (sheafifyMap K η))
    rw [← toSheafify_naturality_assoc, toSheafify_sheafifyLift, ← Category.assoc,
      toSheafify_sheafifyLift, ← (R).map_comp, ← (R).map_comp, toSheafify_naturality]

/-- Before sheafification the comparison is the actual reindexed unit. -/
@[reassoc]
theorem toSheafify_sheafifyReindexComparison (P : Dᵒᵖ ⥤ A) :
    toSheafify J ((R).obj P) ≫ ((F.sheafifyReindexComparison J K A).app P).hom =
      (R).map (toSheafify K P) :=
  toSheafify_sheafifyLift J _ _

end

instance sheafPushforwardContinuous_additive [Preadditive A] : (S).Additive where
  map_add := rfl

variable [Abelian A] [HasSheafify J A] [HasSheafify K A]
variable {ι : Type*} (c : ComplexShape ι)

/-- Apply sheafification to a map into a reindexed complex and then compare
with reindexing the sheafified target. -/
def sheafifyReindexComplexMap
    {M : HomologicalComplex (Cᵒᵖ ⥤ A) c} {N : HomologicalComplex (Dᵒᵖ ⥤ A) c}
    (f : M ⟶ ((R).mapHomologicalComplex c).obj N) :
    ((presheafToSheaf J A).mapHomologicalComplex c).obj M ⟶
      ((S).mapHomologicalComplex c).obj (((presheafToSheaf K A).mapHomologicalComplex c).obj N) :=
  ((presheafToSheaf J A).mapHomologicalComplex c).map f ≫
    (NatTrans.mapHomologicalComplex (F.sheafifyReindexComparison J K A) c).app N

/-- The map of sheafified complexes extends the original map followed by the
reindexed sheafification unit in every degree. -/
@[reassoc]
theorem toSheafify_sheafifyReindexComplexMap_f
    {M : HomologicalComplex (Cᵒᵖ ⥤ A) c} {N : HomologicalComplex (Dᵒᵖ ⥤ A) c}
    (f : M ⟶ ((R).mapHomologicalComplex c).obj N) (i : ι) :
    toSheafify J (M.X i) ≫ ((F.sheafifyReindexComplexMap J K A c f).f i).hom =
      f.f i ≫ (R).map (toSheafify K (N.X i)) := by
  change toSheafify J (M.X i) ≫
      (sheafifyMap J (f.f i) ≫ ((F.sheafifyReindexComparison J K A).app (N.X i)).hom) = _
  rw [← toSheafify_naturality_assoc]
  exact congrArg (fun a : (R).obj (N.X i) ⟶ (R).obj (sheafify K (N.X i)) ↦ f.f i ≫ a)
    (F.toSheafify_sheafifyReindexComparison J K A (N.X i))

end CategoryTheory.Functor
