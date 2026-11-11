/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenPullback
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPairPullback
/-! # Exactness of the original bounded-flat relative-open restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
/-- Original relative-open restriction is exact on the actual bounded-flat complexes. -/
@[colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/PairRestriction.lean:38"
  "adaptation" "Original coarse coefficient exactness, chosen zero and strict restriction."]
theorem boundedAboveFlatPerfectOpenRestriction_exact :
    CategoryTheory.Waldhausen.IsExact (boundedAboveFlatPerfectOpenWaldhausen j).cof
      (boundedAboveFlatPerfectOpenWaldhausen j).weq
      (boundedAboveFlatPerfectWaldhausen U.toRingedSpace).cof (boundedAboveFlatPerfectWaldhausen
        U.toRingedSpace).weq
      (boundedAboveFlatPerfectPullback j) where
  zero := (boundedAboveFlatPerfectPullback_isExact j).zero
  cofibration := (boundedAboveFlatPerfectPullback_isExact j).cofibration
  pushout := (boundedAboveFlatPerfectPullback_isExact j).pushout
  weak {K L} p hp := by
    let : QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map p.hom) := hp
    let e := NatIso.mapHomologicalComplex (restrictFunctorIsoPullback j) (ComplexShape.up ℤ)
    change QuasiIso (((pullback j).mapHomologicalComplex (ComplexShape.up ℤ)).map p.hom)
    exact quasiIso_of_arrow_mk_iso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up
      ℤ)).map p.hom)
      (((pullback j).mapHomologicalComplex (ComplexShape.up ℤ)).map p.hom)
      (Arrow.isoMk (e.app K.obj) (e.app L.obj) (e.hom.naturality p.hom).symm)

end AlgebraicGeometry.Scheme.Modules
