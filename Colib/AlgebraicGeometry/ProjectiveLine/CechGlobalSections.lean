/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.CechSectionsComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportModel.AffinePushforwardSections
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightAcyclicFiniteProduct

/-! # The signed Čech complex over the coefficient ring

The complex is the shifted mapping cone of the actual signed restriction
map on chart sections. Its image in the derived category computes derived
global sections over the coefficient ring.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open AlgebraicGeometry Stacks.AlgebraicGeometry.ProperSupportModel
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections Stacks.Cohomology.AffineComparison

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
attribute [local instance] Functor.isTriangulated_rightDerivedFunctorPlus

variable (R : CommRingCat.{u}) (M : (line R).Modules)

variable [M.IsQuasicoherent]

private theorem rightAcyclic_baseSections_affine {Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ Spec R) (N : Y.Modules) [N.IsQuasicoherent] :
    (baseSections f).rightAcyclic N :=
  Stacks.LeraySections.rightAcyclic_of_exact_comp
    (Stacks.Cohomology.AffineBase.moduleGlobalSections Y) (baseRestrict f) (baseSections f)
    (Iso.refl _) (Stacks.Cohomology.AffineBase.rightAcyclic_moduleGlobalSections Y N)

private theorem rightAcyclic_baseSections_affinePushforward {Y : Scheme.{u}} [IsAffine Y]
    (j : Y ⟶ line R) [IsAffineHom j] (N : Y.Modules) [N.IsQuasicoherent] :
    (baseSections (lineProjection R)).rightAcyclic ((Scheme.Modules.pushforward j).obj N) := by
  let f := lineProjection R
  let P := Scheme.Modules.pushforward j
  let G := baseSections f
  have e : (baseSections (j ≫ f)).rightDerivedFunctorPlus ≅
      P.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
    Functor.rightDerivedFunctorPlusNatIso (baseSectionsCompIso f j) ≪≫
      Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic P G
        (rightAcyclic_baseSections_pushforward f j)
  let J := (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N
  have e' : G.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (line R).Modules 0).obj (P.obj N)) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (G.obj (P.obj N)) :=
    G.rightDerivedFunctorPlus.mapIso
      (rightDerivedFunctorPlusObjSingleIso P N
        (rightAcyclic_pushforward_of_isAffineHom j N)).symm ≪≫
    (e.app J).symm ≪≫
    rightDerivedFunctorPlusObjSingleIso (baseSections (j ≫ f)) N
      (rightAcyclic_baseSections_affine R (j ≫ f) N)
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus G (P.obj N)).2
    inferInstance).2 fun i hi ↦ ?_
  exact (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) i).mapIso e' |>.isZero_iff.mpr
    (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 i hi)

/-- The literal signed complex computes the derived global sections of a
quasi-coherent sheaf on the projective line. -/
def lineCechSectionsComplexIso :
    derivedGlobalSectionsOverBase (lineProjection R) M ≅
      DerivedCategory.Q.obj (lineCechSectionsComplex R M) := by
  let U := lineChartZero R
  let V := lineChartOne R
  let G := baseSections (lineProjection R)
  let S := Scheme.Modules.twoOpenCech U V M
  have hS : S.ShortExact := Scheme.Modules.twoOpenCech_shortExact U V M (lineChart_cover R)
  let hU := rightAcyclic_baseSections_affinePushforward R U.ι (M.restrict U.ι)
  let hV := rightAcyclic_baseSections_affinePushforward R V.ι (M.restrict V.ι)
  have h₂ : G.rightAcyclic S.X₂ := Stacks.RightAcyclicProduct.rightAcyclic_biprod G hU hV
  have h₃ : G.rightAcyclic S.X₃ :=
    rightAcyclic_baseSections_affinePushforward R (U ⊓ V).ι (M.restrict (U ⊓ V).ι)
  let T := G.rightDerivedAcyclicTriangle hS h₂ h₃
  have hT : T ∈ distTriang _ := G.rightDerivedAcyclicTriangle_distinguished hS h₂ h₃
  let E := DerivedCategory.Plus.ι.mapTriangle.obj T
  let C := DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (lineCechSectionsMap R M))
  have e : E.rotate ≅ C := by
    refine isoTriangleOfIso₁₂ _ _
      (rot_of_distTriang _ (DerivedCategory.Plus.ι.map_distinguished _ hT))
      (DerivedCategory.mappingCone_triangle_distinguished _) (Iso.refl _) (Iso.refl _) ?_
    change DerivedCategory.Q.map (lineCechSectionsMap R M) ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id]
    rfl
  exact derivedGlobalSectionsOverBaseIsoPlus (lineProjection R) M ≪≫
    ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ) (-1)
      (by omega)).app _).symm ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (-1 : ℤ)).mapIso
      (Triangle.π₃.mapIso e) ≪≫
    ((DerivedCategory.Q.commShiftIso (-1 : ℤ)).app _).symm

end AlgebraicGeometry.projectiveSpaceOver
