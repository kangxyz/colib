/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Component maps of a triangle comparison through two functors -/

@[expose] public section

open CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]

section

variable (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
  [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
  (e : H ≅ F ⋙ G) [NatTrans.CommShift e.hom ℤ]
  (T : Triangle C) {U : Triangle D} {V : Triangle E}
  (p : F.mapTriangle.obj T ≅ U) (q : G.mapTriangle.obj U ≅ V)

/-- Transport a triangle comparison along the given functor isomorphism and
the canonical comparison for composition of the triangle functors. -/
def mapTriangleComparisonIso : H.mapTriangle.obj T ≅ V :=
  (mapTriangleIso e).app T ≪≫ (mapTriangleCompIso F G).app T ≪≫
    G.mapTriangle.mapIso p ≪≫ q

/-- The first component is the composite of the given first components. -/
theorem mapTriangleComparisonIso_hom₁ :
    (mapTriangleComparisonIso F G e T p q).hom.hom₁ =
      e.hom.app T.obj₁ ≫ 𝟙 (G.obj (F.obj T.obj₁)) ≫ G.map p.hom.hom₁ ≫ q.hom.hom₁ := by
  simp only [mapTriangleComparisonIso, Iso.trans_hom, Iso.app_hom, comp_hom₁,
    mapTriangleIso_hom_app_hom₁, mapTriangleCompIso_hom_app_hom₁, mapIso_hom,
    mapTriangle_map_hom₁]

/-- The second component is the composite of the given second components. -/
theorem mapTriangleComparisonIso_hom₂ :
    (mapTriangleComparisonIso F G e T p q).hom.hom₂ =
      e.hom.app T.obj₂ ≫ 𝟙 (G.obj (F.obj T.obj₂)) ≫ G.map p.hom.hom₂ ≫ q.hom.hom₂ := by
  simp only [mapTriangleComparisonIso, Iso.trans_hom, Iso.app_hom, comp_hom₂,
    mapTriangleIso_hom_app_hom₂, mapTriangleCompIso_hom_app_hom₂, mapIso_hom,
    mapTriangle_map_hom₂]

/-- The third component is the composite of the given third components. -/
theorem mapTriangleComparisonIso_hom₃ :
    (mapTriangleComparisonIso F G e T p q).hom.hom₃ =
      e.hom.app T.obj₃ ≫ 𝟙 (G.obj (F.obj T.obj₃)) ≫ G.map p.hom.hom₃ ≫ q.hom.hom₃ := by
  simp only [mapTriangleComparisonIso, Iso.trans_hom, Iso.app_hom, comp_hom₃,
    mapTriangleIso_hom_app_hom₃, mapTriangleCompIso_hom_app_hom₃, mapIso_hom,
    mapTriangle_map_hom₃]

end

variable (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ]
  {T : Triangle C} {U : Triangle D} {V : Triangle E}
  (p : F.mapTriangle.obj T ≅ U) (q : (F ⋙ G).mapTriangle.obj T ≅ V)

/-- Compare the image of an isomorphic triangle with the given comparison for the
composite functor. -/
def mapTriangleComparisonIsoOfComp : G.mapTriangle.obj U ≅ V :=
  G.mapTriangle.mapIso p.symm ≪≫ (mapTriangleCompIso F G).symm.app T ≪≫ q

/-- The first component is determined by its composite with the mapped first component of `p`. -/
theorem mapTriangleComparisonIsoOfComp_hom₁_of_comp
    (f : G.obj U.obj₁ ⟶ V.obj₁) (h : q.hom.hom₁ = G.map p.hom.hom₁ ≫ f) :
    (mapTriangleComparisonIsoOfComp F G p q).hom.hom₁ = f := by
  change G.map p.inv.hom₁ ≫ 𝟙 (G.obj (F.obj T.obj₁)) ≫ q.hom.hom₁ = f
  exact (congrArg (G.map p.inv.hom₁ ≫ ·) (Category.id_comp q.hom.hom₁)).trans
    ((G.mapIso (Triangle.π₁.mapIso p)).inv_comp_eq.2 h)

/-- The second component is determined by its composite with the mapped second component of `p`. -/
theorem mapTriangleComparisonIsoOfComp_hom₂_of_comp
    (f : G.obj U.obj₂ ⟶ V.obj₂) (h : q.hom.hom₂ = G.map p.hom.hom₂ ≫ f) :
    (mapTriangleComparisonIsoOfComp F G p q).hom.hom₂ = f := by
  change G.map p.inv.hom₂ ≫ 𝟙 (G.obj (F.obj T.obj₂)) ≫ q.hom.hom₂ = f
  exact (congrArg (G.map p.inv.hom₂ ≫ ·) (Category.id_comp q.hom.hom₂)).trans
    ((G.mapIso (Triangle.π₂.mapIso p)).inv_comp_eq.2 h)

/-- The third component is determined by its composite with the mapped third component of `p`. -/
theorem mapTriangleComparisonIsoOfComp_hom₃_of_comp
    (f : G.obj U.obj₃ ⟶ V.obj₃) (h : q.hom.hom₃ = G.map p.hom.hom₃ ≫ f) :
    (mapTriangleComparisonIsoOfComp F G p q).hom.hom₃ = f := by
  change G.map p.inv.hom₃ ≫ 𝟙 (G.obj (F.obj T.obj₃)) ≫ q.hom.hom₃ = f
  exact (congrArg (G.map p.inv.hom₃ ≫ ·) (Category.id_comp q.hom.hom₃)).trans
    ((G.mapIso (Triangle.π₃.mapIso p)).inv_comp_eq.2 h)

end CategoryTheory.Functor
