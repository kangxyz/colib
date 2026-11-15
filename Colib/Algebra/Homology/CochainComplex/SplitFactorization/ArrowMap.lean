/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.AdditiveMap
public import Colib.Algebra.Homology.MappingCone.ShortExact

/-! # Additive comparison of cones of arrows -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace CochainComplex.SplitFactorization

/-- Paste two commuting squares, applying the displayed functor to the second. -/
theorem comp_map_of_commSq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} {A A' : D}
    (u : X ⟶ X') (v : Y ⟶ Y') (b : X ⟶ Y) (b' : X' ⟶ Y')
    (f : A ⟶ A') (a : A ⟶ F.obj X) (a' : A' ⟶ F.obj X')
    (h : u ≫ b' = b ≫ v) (h' : f ≫ a' = a ≫ F.map u) :
    f ≫ (a' ≫ F.map b') = (a ≫ F.map b) ≫ F.map v := by
  rw [← Category.assoc, h', Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc]

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- The original cone comparison commutes with the map of arrows. -/
theorem coneMapIso_naturality_arrow {X Y : Arrow (CochainComplex C ℤ)} (u : X ⟶ Y) :
    let H := F.mapHomologicalComplex (.up ℤ)
    let K := mappingConeNatTransFunctor (Arrow.leftToRight (C := CochainComplex C ℤ))
    let L := mappingConeNatTransFunctor (Arrow.leftToRight (C := CochainComplex D ℤ))
    H.map (K.map u) ≫ (mappingCone.mapHomologicalComplexIso Y.hom F).hom =
      (mappingCone.mapHomologicalComplexIso X.hom F).hom ≫ L.map (H.mapArrow.map u) := by
  dsimp only
  exact coneMapIso_naturality F X.hom Y.hom u.left u.right u.w.symm

/-- A natural transformation of additive functors induces the corresponding arrow map
between their termwise cone comparisons. -/
theorem coneMapIso_naturalTransformation_arrow {G : C ⥤ D} [G.Additive]
    (η : F ⟶ G) (X : Arrow (CochainComplex C ℤ)) :
    let H := F.mapHomologicalComplex (.up ℤ)
    let J := G.mapHomologicalComplex (.up ℤ)
    let τ := η.mapHomologicalComplex (.up ℤ)
    let L := mappingConeNatTransFunctor (Arrow.leftToRight (C := CochainComplex D ℤ))
    let p : H.mapArrow.obj X ⟶ J.mapArrow.obj X :=
      Arrow.homMk' (τ.app X.left) (τ.app X.right) (τ.naturality X.hom).symm
    τ.app (mappingCone X.hom) ≫ (mappingCone.mapHomologicalComplexIso X.hom G).hom =
      (mappingCone.mapHomologicalComplexIso X.hom F).hom ≫ L.map p := by
  dsimp only
  exact coneMapIso_naturalTransformation F η X.hom

end CochainComplex.SplitFactorization
