/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenDiagram

/-! # Integrality of the actual component-system limit

The actual cone vertex is integral because it is the original marked normal component,
not because an arbitrary open of the whole strict-local curve is assumed integral.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The geometric descended-open equality identifies the actual root's integral domain. -/
theorem etaleStageOpenCone_isIntegral
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
    [IsNormal (etaleCurveCone X B hX s p).pt]
    (x : (etaleCurveCone X B hX s p).pt)
    (hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x) :
    IsIntegral (etaleStageOpenCone X s p i U B hX).pt := by
  let e := etaleStageOpenConeNormalComponentIso X s p i U B hX x hpre
  have : Nonempty (etaleStageOpenCone X s p i U B hX).pt :=
    ⟨e.inv ⟨x, mem_normalComponentOpen x⟩⟩
  exact isIntegral_of_isOpenImmersion e.hom

end AlgebraicGeometry.Scheme.SmoothSite
