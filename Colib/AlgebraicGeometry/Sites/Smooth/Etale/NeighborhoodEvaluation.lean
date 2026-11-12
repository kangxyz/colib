/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodPoint
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# Ordinary presheaf values at affine étale neighborhoods

The value is the native point fiber of the original abelian-group presheaf.
Its canonical cocone is a colimit on the actual affine neighborhood diagram.
No value on an arbitrary henselian scheme or rigidity comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  (X : SmoothSite S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ X.left)

local instance : InitiallySmall.{u + 1} (EtaleNeighborhood X ξ) :=
  etaleNeighborhoodInitiallySmall.{u, u + 1} X ξ

/-- The actual native point fiber of the original ordinary presheaf. -/
abbrev etaleNeighborhoodValue (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.obj F

/-- The representative map from an actual affine neighborhood. -/
def toEtaleNeighborhoodValue (A : EtaleNeighborhood X ξ)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A)) ⟶ etaleNeighborhoodValue X ξ F :=
  GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered.{u + 1}
    (etaleNeighborhoodToSmooth X ξ) (etaleNeighborhoodCoverLift X ξ) A F

/-- The canonical cocone on the original presheaf restricted to actual neighborhoods. -/
def etaleNeighborhoodValueCocone (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Cocone ((etaleNeighborhoodToSmooth X ξ).op ⋙ F) :=
  GrothendieckTopology.Point.presheafFiberOfIsCofilteredCocone.{u + 1}
    (etaleNeighborhoodToSmooth X ξ) (etaleNeighborhoodCoverLift X ξ) F

/-- The native point fiber is the colimit of the actual affine neighborhood diagram. -/
@[colib_tag "COL-1057"]
def etaleNeighborhoodValueIsColimit (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsColimit (etaleNeighborhoodValueCocone X ξ F) :=
  GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone.{u + 1}
    (etaleNeighborhoodToSmooth X ξ) (etaleNeighborhoodCoverLift X ξ) F

@[reassoc (attr := simp)]
theorem toEtaleNeighborhoodValue_w {A B : EtaleNeighborhood X ξ} (f : A ⟶ B)
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.map ((etaleNeighborhoodToSmooth X ξ).map f).op ≫ toEtaleNeighborhoodValue X ξ A F =
      toEtaleNeighborhoodValue X ξ B F :=
  GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_w.{u + 1} _ _ f F

@[reassoc (attr := simp)]
theorem toEtaleNeighborhoodValue_naturality
    {F G : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (η : F ⟶ G)
    (A : EtaleNeighborhood X ξ) :
    toEtaleNeighborhoodValue X ξ A F ≫
        (etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map η =
      η.app (op ((etaleNeighborhoodToSmooth X ξ).obj A)) ≫
        toEtaleNeighborhoodValue X ξ A G :=
  GrothendieckTopology.Point.toPresheafFiberOfIsCofiltered_naturality.{u + 1} _ _ η A

local instance : PreservesColimitsOfShape (EtaleNeighborhood X ξ)ᵒᵖ
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{u + 1} _) _

/-- Every value has a representative in an actual affine étale neighborhood. -/
theorem exists_etaleNeighborhood_representative
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (z : etaleNeighborhoodValue X ξ F) :
    ∃ (A : EtaleNeighborhood X ξ)
      (a : F.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A))),
      toEtaleNeighborhoodValue X ξ A F a = z := by
  obtain ⟨A, a, ha⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1})
      (etaleNeighborhoodValueIsColimit X ξ F)) z
  exact ⟨A.unop, a, ha⟩

/-- Two values admit representatives in one actual affine neighborhood. -/
theorem exists_etaleNeighborhood_representatives₂
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (z₁ z₂ : etaleNeighborhoodValue X ξ F) :
    ∃ (A : EtaleNeighborhood X ξ)
      (a₁ a₂ : F.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A))),
      toEtaleNeighborhoodValue X ξ A F a₁ = z₁ ∧
        toEtaleNeighborhoodValue X ξ A F a₂ = z₂ := by
  obtain ⟨A, a₁, a₂, h₁, h₂⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1})
      (etaleNeighborhoodValueIsColimit X ξ F)) z₁ z₂
  exact ⟨A.unop, a₁, a₂, h₁, h₂⟩

/-- Equality is witnessed after an actual common affine étale refinement. -/
@[colib_tag "COL-1057"]
theorem toEtaleNeighborhoodValue_eq_iff
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (A B : EtaleNeighborhood X ξ)
    (a : F.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A)))
    (b : F.obj (op ((etaleNeighborhoodToSmooth X ξ).obj B))) :
    toEtaleNeighborhoodValue X ξ A F a = toEtaleNeighborhoodValue X ξ B F b ↔
      ∃ (C : EtaleNeighborhood X ξ) (f : C ⟶ A) (g : C ⟶ B),
        F.map ((etaleNeighborhoodToSmooth X ξ).map f).op a =
          F.map ((etaleNeighborhoodToSmooth X ξ).map g).op b := by
  constructor
  · intro h
    obtain ⟨C, f, g, hfg⟩ :=
      ((etaleNeighborhoodValueIsColimit X ξ F).eq_iff _).mp h
    exact ⟨C.unop, f.unop, g.unop, hfg⟩
  · rintro ⟨C, f, g, hfg⟩
    exact ((etaleNeighborhoodValueIsColimit X ξ F).eq_iff _).mpr
      ⟨op C, f.op, g.op, hfg⟩

/-- A representative vanishes exactly when it vanishes on a later neighborhood. -/
theorem toEtaleNeighborhoodValue_eq_zero_iff
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (A : EtaleNeighborhood X ξ)
    (a : F.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A))) :
    toEtaleNeighborhoodValue X ξ A F a = 0 ↔
      ∃ (B : EtaleNeighborhood X ξ) (f : B ⟶ A),
        F.map ((etaleNeighborhoodToSmooth X ξ).map f).op a = 0 := by
  have h := (etaleNeighborhoodValueIsColimit X ξ F).eq_iff' a 0
  simp only [map_zero] at h
  constructor
  · intro ha
    obtain ⟨B, f, hf⟩ := h.mp ha
    exact ⟨B.unop, f.unop, hf⟩
  · rintro ⟨B, f, hf⟩
    exact h.mpr ⟨op B, f.op, hf⟩

/-- A common annihilator of the stage groups annihilates their actual value. -/
theorem etaleNeighborhoodValue_nsmul_eq_zero
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ)
    (h : ∀ (A : EtaleNeighborhood X ξ)
      (a : F.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A))), n • a = 0)
    (z : etaleNeighborhoodValue X ξ F) : n • z = 0 := by
  obtain ⟨A, a, rfl⟩ := exists_etaleNeighborhood_representative X ξ F z
  rw [← map_nsmul, h, map_zero]

/-- The canonical comparison from the chosen colimit to the native point fiber. -/
@[colib_tag "COL-1057"]
def etaleNeighborhoodColimitIso (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    colimit ((etaleNeighborhoodToSmooth X ξ).op ⋙ F) ≅ etaleNeighborhoodValue X ξ F :=
  (colimit.isColimit _).coconePointUniqueUpToIso (etaleNeighborhoodValueIsColimit X ξ F)

@[reassoc (attr := simp)]
theorem colimit_ι_etaleNeighborhoodColimitIso_hom
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (A : EtaleNeighborhood X ξ) :
    colimit.ι ((etaleNeighborhoodToSmooth X ξ).op ⋙ F) (op A) ≫
        (etaleNeighborhoodColimitIso X ξ F).hom = toEtaleNeighborhoodValue X ξ A F :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _

/-- Étale sheafification preserves this value through its actual canonical unit. -/
@[colib_tag "COL-1057"]
def etaleNeighborhoodSheafificationIso (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    etaleNeighborhoodValue X ξ F ≅
      etaleNeighborhoodValue X ξ (sheafify (etaleTopology S) F) :=
  asIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
    (toSheafify (etaleTopology S) F))

@[reassoc (attr := simp)]
theorem toEtaleNeighborhoodValue_sheafificationIso_hom
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (A : EtaleNeighborhood X ξ) :
    toEtaleNeighborhoodValue X ξ A F ≫ (etaleNeighborhoodSheafificationIso X ξ F).hom =
      (toSheafify (etaleTopology S) F).app (op ((etaleNeighborhoodToSmooth X ξ).obj A)) ≫
        toEtaleNeighborhoodValue X ξ A (sheafify (etaleTopology S) F) :=
  toEtaleNeighborhoodValue_naturality X ξ _ A

end AlgebraicGeometry.Scheme.SmoothSite
