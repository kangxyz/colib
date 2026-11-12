/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryDiagram

/-! # Noetherian full boundaries of the actual component stages -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The original full boundary at each restarted stage is Noetherian, as a
closed subscheme of the actual Noetherian component stage. -/
instance etaleStageOpenBoundaryDiagram_isNoetherian
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
    {Z : Scheme.{u}} (d : Z ⟶ U.toScheme)
    [IsLocallyNoetherian X.left] [IsProper p] [IsClosedImmersion U.ι]
    [IsClosedImmersion d] (a : Over i) :
    IsNoetherian ((etaleStageOpenBoundaryDiagram X s p i U d).obj a) := by
  let q := (etaleStageOpenBoundaryMap X s p i U d).app a
  have : IsClosedImmersion q := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace ((etaleStageOpenBoundaryDiagram X s p i U d).obj a) :=
    QuasiCompact.compactSpace_of_compactSpace q
  exact ⟨⟩

end AlgebraicGeometry.Scheme.SmoothSite
