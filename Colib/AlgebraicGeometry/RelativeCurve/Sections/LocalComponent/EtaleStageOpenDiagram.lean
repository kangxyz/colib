/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleLimit
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Restarting the actual etale diagram on a specified finite-stage open

A root on a strict-local component is descended on the diagram of that component,
not extended to the whole strict-local curve. The index is the actual over-category
of the selected neighborhood. Its cone is obtained from the original limit cone.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
attribute [local instance] IsCofiltered.isConnected

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)

/-- The actual finite-stage open pulled back to all subsequent original neighborhoods. -/
def etaleStageOpenDiagram : Over i ⥤ Scheme.{u} :=
  Over.post (etaleCurveDiagram X s p) ⋙ Over.pullback U.ι ⋙ Over.forget U.toScheme

/-- A stage is the literal pullback of the chosen open along the original transition. -/
theorem etaleStageOpenDiagram_obj (a : Over i) :
    (etaleStageOpenDiagram X s p i U).obj a =
      pullback ((etaleCurveDiagram X s p).map a.hom) U.ι := rfl

/-- Affine transitions are inherited from the original curve transitions by base change. -/
instance etaleStageOpenDiagram_map_isAffineHom {a b : Over i} (v : a ⟶ b) :
    IsAffineHom ((etaleStageOpenDiagram X s p i U).map v) :=
  MorphismProperty.overPullbackMap (P := @IsAffineHom) U.ι
    ((Over.post (etaleCurveDiagram X s p)).map v) (by
      change IsAffineHom ((etaleCurveDiagram X s p).map v.left)
      infer_instance)

variable (B : BigEtaleSite.{u}) (hX : B.Contains X.left)

/-- Restrict the original cone above the selected stage and then pull back the
specified open. The vertex is not an unspecified limit object. -/
def etaleStageOpenCone : Cone (etaleStageOpenDiagram X s p i U) :=
  (Over.forget U.toScheme).mapCone
    ((Over.pullback U.ι).mapCone ((etaleCurveCone X B hX s p).overPost i))

/-- The restarted diagram has the actual inverse-image open as its limit,
via the literal pullback cone vertex. -/
def etaleStageOpenConeIsLimit : IsLimit (etaleStageOpenCone X s p i U B hX) :=
  isLimitOfPreserves (Over.forget U.toScheme)
    (isLimitOfPreserves (Over.pullback U.ι)
      ((etaleCurveConeIsLimit X B hX s p).overPost i))

/-- The restarted vertex is exactly the original cone projection's pullback of the open. -/
theorem etaleStageOpenCone_pt :
    (etaleStageOpenCone X s p i U B hX).pt =
      pullback ((etaleCurveCone X B hX s p).π.app i) U.ι := rfl

/-- The actual restarted vertex is canonically identified with the actual preimage open. -/
def etaleStageOpenConePreimageIso :
    (etaleStageOpenCone X s p i U B hX).pt ≅
      (((etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U).toScheme) :=
  pullbackRestrictIsoRestrict ((etaleCurveCone X B hX s p).π.app i) U

/-- The preimage identification preserves the original inclusion into the whole
strict-local curve, without extending any module from the component. -/
@[simp, reassoc] theorem etaleStageOpenConePreimageIso_hom_ι :
    (etaleStageOpenConePreimageIso X s p i U B hX).hom ≫
      ((etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U).ι =
    pullback.fst ((etaleCurveCone X B hX s p).π.app i) U.ι :=
  pullbackRestrictIsoRestrict_hom_ι _ _

/-- An actual descended component-open equality identifies this limit with the
original strict-local normal component. The equality is geometric, not a root
extension or frame-compatibility assumption. -/
def etaleStageOpenConeNormalComponentIso
    [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
    [IsNormal (etaleCurveCone X B hX s p).pt]
    (x : (etaleCurveCone X B hX s p).pt)
    (hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x) :
    (etaleStageOpenCone X s p i U B hX).pt ≅ (normalComponentOpen x).toScheme :=
  etaleStageOpenConePreimageIso X s p i U B hX ≪≫
    Scheme.isoOfEq (etaleCurveCone X B hX s p).pt hpre

/-- If the selected finite-stage open is also closed, every restarted stage is
Noetherian by closed base change from the original proper curve stage. -/
instance etaleStageOpenDiagram_isNoetherian [IsLocallyNoetherian X.left] [IsProper p]
    [IsClosedImmersion U.ι] (a : Over i) :
    IsNoetherian ((etaleStageOpenDiagram X s p i U).obj a) := by
  let q := pullback.fst ((etaleCurveDiagram X s p).map a.hom) U.ι
  have : IsClosedImmersion q := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace (pullback ((etaleCurveDiagram X s p).map a.hom) U.ι : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace q
  change IsNoetherian (pullback ((etaleCurveDiagram X s p).map a.hom) U.ι)
  exact ⟨⟩

end AlgebraicGeometry.Scheme.SmoothSite
