/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRetainedSections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitEmbedding
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitIntegral
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryFinite
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitSameClosedFibre
public import Colib.AlgebraicGeometry.EtaleCohomology.SameFibreCartesianRootAuxiliaryFullBoundary

/-! # The same-root supplier on an actual component stage and its actual limit

All local/stage curves, sections, retained opens, full boundaries and cone maps
are the existing objects. Projective embedding and closed-fibre coincidence are
constructed, not supplied as compatibility certificates. The only prescribed
frame is the input stage frame (in the application, its canonical difference frame).
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
open Stacks.Divisors Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance actualStageSupplierRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance actualStageSupplierPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance actualStageSupplierUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)



/-- Construct the original strict-local root and auxiliary pair on the actual
component cone, with target pulled back from the actual selected stage a0. -/
theorem etaleStageOpen_exists_actual_root_auxiliary
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    [IsLocallyNoetherian X.left] [IsProper p]
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    [IsClosedImmersion U.ι]
    [IsSeparated (U.ι ≫ (etaleCurveStructure X s p).app i)]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
    [IsNormal (etaleCurveCone X B hX s p).pt]
    (x : (etaleCurveCone X B hX s p).pt)
    (hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x)
    (hp : IsProjectiveMorphism p)
    {V Z : Scheme.{u}} [IsAffine V]
    (j : V ⟶ U.toScheme) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (d : Z ⟶ U.toScheme) [IsClosedImmersion d]
    [IsFinite (d ≫ U.ι ≫ (etaleCurveStructure X s p).app i)]
    (hd : Set.range d = (Set.range j)ᶜ)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hσj : Set.range σ ⊆ Set.range j) (hτj : Set.range τ ⊆ Set.range j)
    (a0 : Over i)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U σ hσ a0 =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U τ hτ a0)
    (τStage : (Scheme.Modules.pullback ((etaleStageOpenBoundaryMap X s p i U d).app a0)).obj
        (differenceSheaf (etaleStageOpenSection X s p i U σ hσ a0).ker
          (etaleStageOpenSection X s p i U τ hτ a0).ker) ≅
      SheafOfModules.unit ((etaleStageOpenBoundaryDiagram X s p i U d).obj a0).ringCatSheaf)
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : ↥(etaleLocalRing B X.left hX s))) :
    let C := (etaleStageOpenCone X s p i U B hX).pt
    let ZL := (etaleStageOpenBoundaryCone X s p i U d B hX).pt
    let iL := etaleStageOpenBoundaryLimitMap X s p i U d B hX
    let f := (etaleStageOpenCone X s p i U B hX).π.app a0
    let D := (etaleStageOpenSection X s p i U σ hσ a0).ker
    let E := (etaleStageOpenSection X s p i U τ hτ a0).ker
    let τL := pullbackBoundaryTrivialization
      ((etaleStageOpenBoundaryCone X s p i U d B hX).π.app a0)
      ((etaleStageOpenBoundaryMap X s p i U d).app a0) iL f
      (etaleStageOpenBoundaryCone_square X s p i U d B hX a0)
      (differenceSheaf D E) τStage
    ∃ (M : C.Modules)
      (hM : Stacks.SheafOfModules.IsInvertible C.presheaf C.ringCatIsSheaf M),
      let _ := hM
      let _ : AlgebraicGeometry.SheafOfModules.IsInvertible C.toRingedSpace.presheaf
          (structureSheafRing C.toRingedSpace).property M := hM.toAlgebraicGeometry
      ∃ (α : tensorPower C.toRingedSpace.presheaf
          (structureSheafRing C.toRingedSpace).property M (n : ℤ) ≅
          (Scheme.Modules.pullback f).obj (differenceSheaf D E))
        (e : (Scheme.Modules.pullback iL).obj M ≅ SheafOfModules.unit ZL.ringCatSheaf),
        tensorPowerCongr ZL.presheaf (ringSheafCond ZL) _ _ e n =
          boundaryRootPowerIso iL M _ n α τL ∧
        ∃ (Naux : C.Modules)
          (_hNaux : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj
            C.ringCatSheaf.property Naux)
          (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor C.sheaf).obj M).obj Naux, ⊤))
          (bN : Γ(Naux, ⊤))
          (eN : (Scheme.Modules.pullback iL).obj Naux ≅ SheafOfModules.unit ZL.ringCatSheaf),
          a ≠ 0 ∧ bN ≠ 0 ∧
          Scheme.Modules.Hom.app (X := ZL) (Scheme.Modules.pullbackTensorFrame iL M Naux e eN).hom ⊤
            (pullbackGlobalSections iL _ a) = (1 : Γ(ZL, ⊤)) ∧
          Scheme.Modules.Hom.app (X := ZL) eN.hom ⊤ (pullbackGlobalSections iL Naux bN) =
            (1 : Γ(ZL, ⊤)) := by
  let R := ↥(etaleLocalRing B X.left hX s)
  let := isNoetherian_strictHenselization B X.left hX s
  let : IsNoetherianRing R := isLocallyNoetherian_Spec.mp
    (inferInstance : IsLocallyNoetherian (strictHenselization B X.left hX s))
  let := etaleStageOpenCone_isIntegral X s p i U B hX x hpre
  let : IsSeparated ((etaleStageOpenStructure X s p i U).app a0) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (etaleStageOpenStructure_isPullback X s p i U a0) inferInstance
  obtain ⟨m, embedding, hemb⟩ :=
    etaleStageOpenLimit_exists_projective_embedding X s p i U B hX hp
  let := hemb
  have hσstage := etaleStageOpenSection_range_retained X s p i U j σ hσ hσj a0
  have hτstage := etaleStageOpenSection_range_retained X s p i U j τ hτ hτj a0
  have hσlocal := etaleStageOpenLimitSection_range_retained X s p i U j σ hσ hσj B hX
  have hτlocal := etaleStageOpenLimitSection_range_retained X s p i U j τ hτ hτj B hX
  have hclosed := etaleStageOpenLimitSection_same_closed_fibre
    X s p i U B hX σ τ hσ hτ a0 hmark
  obtain ⟨M, hM, αLocal, e, he, Naux, hNaux, a, bN, eN, ha, hbN, haB, hbB⟩ :=
    Stacks.Kummer.exists_sameFibreSectionKernel_cartesian_root_auxiliaryFrames_fullBoundary
      R m embedding
      ((etaleStageOpenCone X s p i U B hX).π.app a0)
      (etaleStageOpenLimitStructure X s p i U B hX)
      ((etaleStageOpenStructure X s p i U).app a0)
      ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a0.left)
      (etaleStageOpenCone_isPullback X s p i U B hX a0)
      ((etaleStageOpenBoundaryMap X s p i U j).app a0)
      (etaleStageOpenBoundaryLimitMap X s p i U j B hX)
      (etaleStageOpenSection X s p i U σ hσ a0)
      (etaleStageOpenSection X s p i U τ hτ a0)
      (etaleStageOpenLimitSection X s p i U B hX σ hσ)
      (etaleStageOpenLimitSection X s p i U B hX τ hτ)
      (etaleStageOpenSection_structure X s p i U σ hσ a0)
      (etaleStageOpenSection_structure X s p i U τ hτ a0)
      (etaleStageOpenLimitSection_structure X s p i U B hX σ hσ)
      (etaleStageOpenLimitSection_structure X s p i U B hX τ hτ)
      (etaleStageOpenLimitSection_comp X s p i U B hX σ hσ a0)
      (etaleStageOpenLimitSection_comp X s p i U B hX τ hτ a0)
      hσstage hτstage hσlocal hτlocal hclosed
      ((etaleStageOpenBoundaryCone X s p i U d B hX).π.app a0)
      (etaleStageOpenBoundaryLimitMap X s p i U d B hX)
      ((etaleStageOpenBoundaryMap X s p i U d).app a0)
      (etaleStageOpenRetained_limit_cover X s p i U j B hX d hd)
      (etaleStageOpenBoundaryCone_square X s p i U d B hX a0) τStage hn0 hn
  let := hM
  refine ⟨M, hM, _, e, he, Naux, hNaux, a, bN, eN, ha, hbN, haB, hbB⟩

end AlgebraicGeometry.Scheme.SmoothSite
