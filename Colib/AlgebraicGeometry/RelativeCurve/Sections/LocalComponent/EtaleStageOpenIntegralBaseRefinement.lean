/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleIntegralBase
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSections

/-! # Integral affine base refinement after the actual descended stage

The new neighborhood belongs to the original neighborhood category. It need not
be an object of the selected small model. Its actual map g gives the literal
curve base change Cnew=pullback q g and F=pullback.fst q g. Already descended
root and auxiliary data are pulled back along this F before selecting a curve
component; neither the small stage nor Cnew is asserted to be integral.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)

/-- Every actual open-component stage is normal when the original curve is normal.
This assertion does not assert connectedness or integrality of the stage. -/
instance etaleStageOpenDiagram_isNormal [IsNormal N] (a : Over i) :
    IsNormal ((etaleStageOpenDiagram X s p i U).obj a) := by
  change IsNormal (pullback ((etaleCurveDiagram X s p).map a.hom) U.ι)
  exact isNormal_of_etale (pullback.fst ((etaleCurveDiagram X s p).map a.hom) U.ι)

/-- Refine the base of the specified final stage to its original marked integral
component. The first curve pullback is literally along the returned clopen g;
its projection F is retained for transporting the same root and auxiliary pair. -/
theorem etaleStageOpen_exists_integral_base_refinement
    [IsNormal X.left] [IsLocallyNoetherian X.left]
    [IsNormal N] [IsProper p] [IsClosedImmersion U.ι] (a : Over i) :
    ∃ (Anew : EtaleNeighborhood X s.hom)
      (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj a.left),
      let baseNew := ((etaleNeighborhoodToSmooth X s.hom).obj Anew).left
      let g := ((etaleNeighborhoodToSmooth X s.hom).map v).left
      let q := (etaleStageOpenStructure X s p i U).app a
      let Cnew := pullback q g
      let F := pullback.fst q g
      let qnew := pullback.snd q g
      IsAffine baseNew ∧ IsIntegral baseNew ∧ IsNoetherian baseNew ∧
      IsOpenImmersion g ∧ IsClosedImmersion g ∧
      IsOpenImmersion F ∧ IsClosedImmersion F ∧
      IsNormal Cnew ∧ IsNoetherian Cnew ∧
      IsPullback F qnew q g ∧
      etaleNeighborhoodMark X s.hom Anew ≫ g =
        etaleNeighborhoodMark X s.hom
          ((smallEtaleNeighborhoodInclusion X s).obj a.left) := by
  obtain ⟨Anew, v, hIntegral, hNoetherian, hOpen, hClosed, _⟩ :=
    exists_integral_etaleNeighborhood_refinement X s.hom
      ((smallEtaleNeighborhoodInclusion X s).obj a.left)
  let baseNew := ((etaleNeighborhoodToSmooth X s.hom).obj Anew).left
  let g := ((etaleNeighborhoodToSmooth X s.hom).map v).left
  let q := (etaleStageOpenStructure X s p i U).app a
  let F := pullback.fst q g
  let := hOpen
  let := hClosed
  have hFOpen : IsOpenImmersion F := inferInstance
  have hFClosed : IsClosedImmersion F := inferInstance
  have hNormal : IsNormal (pullback q g) := isNormal_of_etale F
  have hNoeth : IsNoetherian (pullback q g) := by
    have := LocallyOfFiniteType.isLocallyNoetherian F
    have : CompactSpace (pullback q g : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace F
    exact ⟨⟩
  exact ⟨Anew, v, inferInstance, hIntegral, hNoetherian, hOpen, hClosed,
    hFOpen, hFClosed, hNormal, hNoeth, IsPullback.of_hasPullback q g,
    etaleNeighborhoodMark_map X s.hom v⟩

end AlgebraicGeometry.Scheme.SmoothSite
