module

import Colib.AlgebraicGeometry.Correspondences.Category.Objects

open AlgebraicGeometry CategoryTheory

universe u

variable (k : Type u) [Field k]

example (X : Scheme.SmoothSite (Spec (.of k))) : (Cor.mk X).toSmoothSite = X := rfl

example (X : Cor k) : CompactSpace X.toSmoothSite.left := inferInstance

example (X : Cor k) : Smooth X.toSmoothSite.hom := inferInstance

example (X : Cor k) : IsSeparated X.toSmoothSite.hom := inferInstance

example (X : Cor k) : QuasiCompact X.toSmoothSite.hom := inferInstance
