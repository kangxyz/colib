/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ClosedPoints
import Colib.AlgebraicGeometry.Sites.Smooth.Etale.StrictHenselization

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable section

variable (k : Type u) [Field k]

-- No algebraic-closedness or rational-point assumption is imposed on the base field.
example :
    (closedEtaleNeighborhoodPointFamily (Spec (.of k))).IsConservativeFamilyOfPoints :=
  isConservativeFamilyOfPoints_closedEtaleNeighborhood _

example : ObjectProperty.Small.{u + 1}
    (closedEtaleNeighborhoodPointFamily (Spec (.of k))) := inferInstance

example : closedEtaleNeighborhoodPointFamily (Spec (.of k)) ≤
    etaleNeighborhoodPointFamily (Spec (.of k)) :=
  closedEtaleNeighborhoodPointFamily_le _

variable {k}
  {F G : Sheaf (etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}} (f : F ⟶ G)

example (h : ∀ (X : Scheme.SmoothSite (Spec (.of k))) (x : X.left),
    IsClosed ({x} : Set X.left) →
      IsIso ((etaleNeighborhoodPoint.{u, u + 1} X
        (GeometricPoint.ofPoint X.left x).hom).presheafFiber.map f.hom)) : IsIso f :=
  (isIso_iff_closedResidueGeometricNeighborhoodValue f).mpr h

example (h : ∀ (X : Scheme.SmoothSite (Spec (.of k))) (s : GeometricPoint X.left),
    IsClosed ({s.hom default} : Set X.left) →
      IsIso ((etaleNeighborhoodPoint.{u, u + 1} X s.hom).presheafFiber.map f.hom)) : IsIso f :=
  (isIso_iff_closedGeometricEtaleNeighborhoodValue f).mpr h

-- These are the original maps on the original geometric-neighborhood diagram.
example (X : Scheme.SmoothSite (Spec (.of k))) (x : closedPoints X.left)
    (A : EtaleNeighborhood X (GeometricPoint.ofPoint X.left x.1).hom) :
    toEtaleNeighborhoodValue X (GeometricPoint.ofPoint X.left x.1).hom A F.obj ≫
        (etaleNeighborhoodPoint.{u, u + 1} X
          (GeometricPoint.ofPoint X.left x.1).hom).presheafFiber.map f.hom =
      f.hom.app (op ((etaleNeighborhoodToSmooth X
          (GeometricPoint.ofPoint X.left x.1).hom).obj A)) ≫
        toEtaleNeighborhoodValue X (GeometricPoint.ofPoint X.left x.1).hom A G.obj :=
  toEtaleNeighborhoodValue_naturality X (GeometricPoint.ofPoint X.left x.1).hom f.hom A

-- Cover detection produces a sieve in the original smooth étale topology.
example (X : Scheme.SmoothSite (Spec (.of k))) (R : Sieve X)
    (hR : ∀ x : closedPoints X.left, ∃ (Y : Scheme.SmoothSite (Spec (.of k))) (g : Y ⟶ X),
      R g ∧ Etale g.left ∧ ∃ y : Y.left, g.left y = x.1) :
    R ∈ etaleTopology (Spec (.of k)) X := by
  let : JacobsonSpace X.left :=
    LocallyOfFiniteType.jacobsonSpace (show X.left ⟶ Spec (.of k) from X.hom)
  exact mem_etaleTopology_of_covers_closedPoints R hR

-- The closed-point restriction retains the same native markings as COL-1082.
example (X : Scheme.SmoothSite (Spec (.of k))) (x : closedPoints X.left)
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left) :
    IsLimit (etaleNeighborhoodStrictHenselizationCone X B hX
      (GeometricPoint.ofPoint X.left x.1)) :=
  etaleNeighborhoodStrictHenselizationConeIsLimit X B hX (GeometricPoint.ofPoint X.left x.1)

example (X : Scheme.SmoothSite (Spec (.of k))) (x : closedPoints X.left)
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (A : EtaleNeighborhood X (GeometricPoint.ofPoint X.left x.1).hom) :
    geometricPointToStrictHenselization B X.left hX (GeometricPoint.ofPoint X.left x.1) ≫
        (etaleNeighborhoodStrictHenselizationCone X B hX
          (GeometricPoint.ofPoint X.left x.1)).π.app A =
      etaleNeighborhoodMark X (GeometricPoint.ofPoint X.left x.1).hom A :=
  geometricPointToStrictHenselization_comp_etaleNeighborhoodCone_π X B hX
    (GeometricPoint.ofPoint X.left x.1) A

#print axioms AlgebraicGeometry.Scheme.SmoothSite.closedEtaleNeighborhoodPointFamily
#print axioms AlgebraicGeometry.Scheme.SmoothSite.closedEtaleNeighborhoodPointFamily_le
#print axioms AlgebraicGeometry.Scheme.SmoothSite.mem_etaleTopology_of_covers_closedPoints
#print axioms AlgebraicGeometry.Scheme.SmoothSite.isConservativeFamilyOfPoints_closedEtaleNeighborhood
#print axioms AlgebraicGeometry.Scheme.SmoothSite.isIso_iff_closedResidueGeometricNeighborhoodValue
#print axioms AlgebraicGeometry.Scheme.SmoothSite.isIso_iff_closedGeometricEtaleNeighborhoodValue
