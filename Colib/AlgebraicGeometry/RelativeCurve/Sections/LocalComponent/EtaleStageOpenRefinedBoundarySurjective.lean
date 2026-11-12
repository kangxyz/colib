/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRefinementCartesian
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenBoundaryDiagram
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualCartesianFullBoundarySurjective
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualStageBoundaryPullbackTransport

/-! # Full boundary surjectivity on the actual refined etale component

The native rings are those of the original affine neighborhoods. The Cartesian
square is constructed, the base ring is not reselected, and the final boundary
is literally the original stage boundary pulled back along F and then kappa.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  [IsLocallyNoetherian X.left] [IsNormal N] [IrreducibleSpace N] [IsProper p]
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  [IsClosedImmersion U.ι]
  (a : Over i) (Anew : EtaleNeighborhood X s.hom)
  (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj a.left)
  [IsIntegral ((etaleNeighborhoodToSmooth X s.hom).obj Anew).left]
  [IsClosedImmersion (((etaleNeighborhoodToSmooth X s.hom).map v).left)]

/-- The exact native ring of the fixed affine neighborhood, without changing its model. -/
abbrev etaleStageOpenFixedRing : CommRingCat.{u} :=
  ((smallEtaleNeighborhoodInclusion X s).obj i).obj.left.unop

local notation "Ai" => etaleStageOpenFixedRing X s i
local notation "Rnew" => Anew.obj.left.unop

local instance refinedBoundaryCurveNormal :
    IsNormal (pullback ((etaleStageOpenStructure X s p i U).app a)
      (((etaleNeighborhoodToSmooth X s.hom).map v).left)) := by
  have hg : Etale (((etaleNeighborhoodToSmooth X s.hom).map v).left) := by
    change Etale (((AffineEtale.Spec X.left).map v.hom).left)
    infer_instance
  exact isNormal_of_etale (pullback.fst ((etaleStageOpenStructure X s p i U).app a)
    (((etaleNeighborhoodToSmooth X s.hom).map v).left))

local instance refinedBoundaryCurveLocallyNoetherian :
    IsLocallyNoetherian (pullback ((etaleStageOpenStructure X s p i U).app a)
      (((etaleNeighborhoodToSmooth X s.hom).map v).left)) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst ((etaleStageOpenStructure X s p i U).app a)
      (((etaleNeighborhoodToSmooth X s.hom).map v).left))

/-- Apply the original independent chart argument to the actual Cnew and its own
normal component. Only the fixed-U finite cover/chart geometry is an input. -/
theorem etaleStageOpen_refined_component_boundary_surjective
    (π : U.toScheme ⟶ projectiveLine Ai) [IsFinite π]
    (hπ : π ≫ (projectiveLine Ai ↘ Spec (.of ↥Ai)) =
      U.ι ≫ (etaleCurveStructure X s p).app i)
    {Y Z E : Scheme.{u}} (j : Y ⟶ U.toScheme)
    (cY : Y ⟶ Spec (.of (Polynomial Ai)))
    (hcY : cY ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : Ai →+* Polynomial Ai)) =
      j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))
    (hj : j ≫ π = cY ≫ projectiveLineXChart Ai)
    (r : U.toScheme ⟶ N) [Flat r]
    (e : E ⟶ N) [IsOpenImmersion e] [Nonempty E]
    (cE : pullback r e ⟶ Spec (.of (Polynomial Ai))) [Etale cE]
    (hcE : cE ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : Ai →+* Polynomial Ai)) =
      pullback.fst r e ≫ (U.ι ≫ (etaleCurveStructure X s p).app i))
    (he : pullback.fst r e ≫ π = cE ≫ projectiveLineXChart Ai)
    (d : Z ⟶ U.toScheme) (hd : Set.range d = (Set.range j)ᶜ)
    (x : (pullback ((etaleStageOpenStructure X s p i U).app a)
      (((etaleNeighborhoodToSmooth X s.hom).map v).left) : Scheme.{u})) :
    let g := ((etaleNeighborhoodToSmooth X s.hom).map v).left
    let q := (etaleStageOpenStructure X s p i U).app a
    let F := pullback.fst q g
    let κ := (normalComponentOpen x).ι
    Surjective (pullback.fst κ
      (pullback.fst F ((etaleStageOpenBoundaryMap X s p i U d).app a)) ≫
      κ ≫ pullback.snd q g) := by
  intro g q F κ
  let : IsDomain Rnew := isDomain_etaleNeighborhood_ring X s.hom Anew
  have hg : Etale g := by
    change Etale (((AffineEtale.Spec X.left).map v.hom).left)
    infer_instance
  let : IsClosedImmersion F := inferInstanceAs (IsClosedImmersion (pullback.fst q g))
  let : IsNormal (pullback q g) := isNormal_of_etale F
  let : IsLocallyNoetherian (pullback q g) := LocallyOfFiniteType.isLocallyNoetherian F
  let rStage := pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι
  let vTotal := F ≫ rStage
  let qnew := pullback.snd q g
  let pU := U.ι ≫ (etaleCurveStructure X s p).app i
  let baseMap := g ≫ (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom
  have hcart : IsPullback vTotal qnew pU baseMap :=
    etaleStageOpenRefinement_fixed_isPullback X s p i U a Anew v
  let : Etale vTotal := etaleStageOpenRefinement_fixed_etale X s p i U a Anew v
  obtain ⟨φ, hφ⟩ := Spec.map_surjective baseMap
  have hcartRing : IsPullback vTotal qnew pU (Spec.map (CommRingCat.ofHom φ.hom)) := by
    change IsPullback vTotal qnew pU (Spec.map φ)
    rw [hφ]
    exact hcart
  have hsurj : Surjective (pullback.fst κ (pullback.fst vTotal d) ≫ κ ≫ qnew) :=
    surjective_actualCartesian_component_fullBoundary (A := ↥Ai) (R := ↥Rnew)
      pU φ.hom vTotal qnew hcartRing
      π hπ j cY hcY hj r e cE hcE he d hd x
  let := hsurj
  exact surjective_actual_stage_boundary_pullbacks rStage d
    ((etaleStageOpenBoundaryMap X s p i U d).app a)
    (pullback.snd ((etaleCurveDiagram X s p).map a.hom) (d ≫ U.ι))
    (etaleStageOpenBoundaryMap_isPullback X s p i U d a) F κ qnew

end AlgebraicGeometry.Scheme.SmoothSite
