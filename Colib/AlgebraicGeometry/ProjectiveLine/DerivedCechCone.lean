/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DerivedCechTriangle

/-! # The signed Čech cone on the projective line -/

public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated HomologicalComplex

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

local instance (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

variable (R : CommRingCat.{u}) (M : (line R).Modules) [M.IsQuasicoherent]

/-- The degree-zero cochain map induced by the actual signed Čech differential. -/
@[expose] def lineCechCochainMap :=
  (single (Spec R).Modules (.up ℤ) 0).map
    ((Scheme.Modules.pushforward (lineProjection R)).map
      (Scheme.Modules.twoOpenCech (lineChartZero R) (lineChartOne R) M).g)

/-- Rotate the original derived Čech triangle and compare it with the signed cone triangle.
The first two components are identities. -/
def lineDerivedCechConeTriangleIso :
    ((DerivedCategory.Plus.ι.mapTriangle).obj (lineDerivedCechTriangle R M)).rotate ≅
      DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (lineCechCochainMap R M)) := by
  refine isoTriangleOfIso₁₂ _ _
    (rot_of_distTriang _ (DerivedCategory.Plus.ι.map_distinguished _
      (lineDerivedCechTriangle_distinguished R M)))
    (DerivedCategory.mappingCone_triangle_distinguished _) (Iso.refl _) (Iso.refl _) ?_
  change DerivedCategory.Plus.ι.map (lineDerivedCechTriangle R M).mor₂ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp only [Category.comp_id]
  rw [lineDerivedCechTriangle_mor₂]
  rfl

/-- The original source term of the signed difference is unchanged. -/
theorem lineDerivedCechConeTriangleIso_hom_hom₁ :
    (lineDerivedCechConeTriangleIso R M).hom.hom₁ = 𝟙 _ := by
  unfold lineDerivedCechConeTriangleIso
  exact isoTriangleOfIso₁₂_hom_hom₁ ..

/-- The original overlap term of the signed difference is unchanged. -/
theorem lineDerivedCechConeTriangleIso_hom_hom₂ :
    (lineDerivedCechConeTriangleIso R M).hom.hom₂ = 𝟙 _ := by
  unfold lineDerivedCechConeTriangleIso
  exact isoTriangleOfIso₁₂_hom_hom₂ ..

/-- The comparison retains the actual derived connecting morphism. -/
theorem lineDerivedCechConeTriangleIso_connecting :
    ((DerivedCategory.Plus.ι.mapTriangle).obj (lineDerivedCechTriangle R M)).mor₃ ≫
        (lineDerivedCechConeTriangleIso R M).hom.hom₃ =
      (DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (lineCechCochainMap R M))).mor₂ := by
  have e := (lineDerivedCechConeTriangleIso R M).hom.comm₂
  exact e.trans ((congrArg
    (fun a ↦ a ≫ (DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle (lineCechCochainMap R M))).mor₂)
    (lineDerivedCechConeTriangleIso_hom_hom₂ R M)).trans (Category.id_comp _))

/-- The derived direct image is the signed two-term Čech cone shifted by minus one. -/
def lineDerivedCechConeIso :
    DerivedCategory.Plus.ι.obj (lineDerivedCechTriangle R M).obj₁ ≅
      DerivedCategory.Q.obj
        ((CochainComplex.mappingCone (lineCechCochainMap R M))⟦(-1 : ℤ)⟧) :=
  ((shiftFunctorCompIsoId (DerivedCategory (Spec R).Modules) (1 : ℤ) (-1)
    (by omega)).app _).symm ≪≫
    (shiftFunctor (DerivedCategory (Spec R).Modules) (-1 : ℤ)).mapIso
      (Triangle.π₃.mapIso (lineDerivedCechConeTriangleIso R M)) ≪≫
    ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).app _).symm

end AlgebraicGeometry.projectiveSpaceOver
