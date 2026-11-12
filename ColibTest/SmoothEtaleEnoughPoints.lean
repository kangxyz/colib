/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.EnoughPoints
import Colib.AlgebraicGeometry.Sites.Smooth.Etale.StrictHenselization

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable section

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {F G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G)

example : GrothendieckTopology.HasEnoughPoints.{u + 1} (etaleTopology S) := inferInstance

example : ObjectProperty.Small.{u + 1} (etaleNeighborhoodPointFamily S) := inferInstance

example (h : ∀ (X : Scheme.SmoothSite S) (s : GeometricPoint X.left),
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} X s.hom).presheafFiber.map f.hom)) :
    IsIso f :=
  (isIso_iff_geometricEtaleNeighborhoodValue f).mpr h

example (h : ∀ (X : Scheme.SmoothSite S) (x : X.left),
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} X
      (GeometricPoint.ofPoint X.left x).hom).presheafFiber.map f.hom)) : IsIso f :=
  (isIso_iff_residueGeometricNeighborhoodValue f).mpr h

example (h : ∀ (X : Scheme.SmoothSite S) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X.left),
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map f.hom)) :
    IsIso f :=
  (isIso_iff_etaleNeighborhoodValue f).mpr h

example (X : Scheme.SmoothSite S) (s : GeometricPoint X.left) :
    etaleNeighborhoodValue X s.hom F.obj ⟶ etaleNeighborhoodValue X s.hom G.obj :=
  (etaleNeighborhoodPoint.{u, u + 1} X s.hom).presheafFiber.map f.hom

example (X : Scheme.SmoothSite S) (s : GeometricPoint X.left)
    (A : EtaleNeighborhood X s.hom) :
    toEtaleNeighborhoodValue X s.hom A F.obj ≫
        (etaleNeighborhoodPoint.{u, u + 1} X s.hom).presheafFiber.map f.hom =
      f.hom.app (op ((etaleNeighborhoodToSmooth X s.hom).obj A)) ≫
        toEtaleNeighborhoodValue X s.hom A G.obj :=
  toEtaleNeighborhoodValue_naturality X s.hom f.hom A

-- The selected conservative family uses the same native geometric points as the limit bridge.
example (X : Scheme.SmoothSite S) (x : X.left) (B : BigEtaleSite.{u})
    (hX : B.Contains X.left) :
    IsLimit (etaleNeighborhoodStrictHenselizationCone X B hX (GeometricPoint.ofPoint X.left x)) :=
  etaleNeighborhoodStrictHenselizationConeIsLimit X B hX (GeometricPoint.ofPoint X.left x)

example (X : Scheme.SmoothSite S) (x : X.left) (B : BigEtaleSite.{u})
    (hX : B.Contains X.left)
    (A : EtaleNeighborhood X (GeometricPoint.ofPoint X.left x).hom) :
    geometricPointToStrictHenselization B X.left hX (GeometricPoint.ofPoint X.left x) ≫
        (etaleNeighborhoodStrictHenselizationCone X B hX
          (GeometricPoint.ofPoint X.left x)).π.app A =
      etaleNeighborhoodMark X (GeometricPoint.ofPoint X.left x).hom A :=
  geometricPointToStrictHenselization_comp_etaleNeighborhoodCone_π X B hX
    (GeometricPoint.ofPoint X.left x) A

#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodPointFamily
#print axioms AlgebraicGeometry.Scheme.SmoothSite.isConservativeFamilyOfPoints_etaleNeighborhood
#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleTopology_hasEnoughPoints_succ
#print axioms AlgebraicGeometry.Scheme.SmoothSite.isIso_iff_residueGeometricNeighborhoodValue
#print axioms AlgebraicGeometry.Scheme.SmoothSite.isIso_iff_geometricEtaleNeighborhoodValue
#print axioms AlgebraicGeometry.Scheme.SmoothSite.isIso_iff_etaleNeighborhoodValue
