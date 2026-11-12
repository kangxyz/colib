/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodPoint

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable example {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : Scheme.SmoothSite S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left) :
    (etaleTopology S).Point.{u + 1} := etaleNeighborhoodPoint.{u, u + 1} X ξ

#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodPoint
#print axioms AlgebraicGeometry.Scheme.SmoothSite.etaleNeighborhoodCoverLift
