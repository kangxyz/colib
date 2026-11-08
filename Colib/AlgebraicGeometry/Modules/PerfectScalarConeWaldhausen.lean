/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectScalarCone
public import Colib.AlgebraicGeometry.Modules.PerfectExactFunctor
public import Colib.AlgebraicGeometry.Modules.PerfectOpenSupport
public import Colib.Algebra.Homology.MappingCone.WeakMap

/-! # Exactness of the original scalar-cone functor

The original signed cones and cone maps preserve native ambient-monomorphism
cofibrations, actual quasi-isomorphisms and their pushouts. A scalar restricting
to the specified forward unit gives the same functor into supported and relative
acyclic complexes. No regularity or fine-open localization is assumed.

Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/ScalarConeFunctor.lean:40-93
at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen Fibration CochainComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u

/-- The literal signed scalar cone is exact for the native perfect Waldhausen structure. -/
theorem perfectScalarConeFunctor_waldhausenExact (X : Scheme.{u}) (r : Γ(X, ⊤)) :
    IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (perfectScalarConeFunctor X r) :=
  RingedSpace.perfectComplexes_lift_isExact X.toRingedSpace _
    (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace) _
    (perfectScalarConeFunctor_shortExact X r) (fun g hg => by
      let : QuasiIso g.hom := hg
      change QuasiIso (((perfectScalarConeFunctor X r).map g).hom)
      rw [perfectScalarConeFunctor_map]
      exact mappingCone_map_quasiIso _ _ _ _ _)

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- Adding the actual support proof preserves exactness and all original maps. -/
theorem perfectSupportedScalarConeFunctor_waldhausenExact :
    IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
      (perfectSupportedScalarConeFunctor j r q hq) := by
  let : (perfectSupportedScalarConeFunctor j r q hq).Additive :=
    perfectSupportedScalarConeFunctor_additive j r q hq
  exact RingedSpace.perfectComplexes_lift_isExact X.toRingedSpace _
    (perfectSupported_cofibrationClosed j) _
    (perfectSupportedScalarConeFunctor_shortExact j r q hq) (fun g hg => by
      let : QuasiIso g.hom := hg
      change QuasiIso (mappingCone.map _ _ g.hom g.hom
        ((complexGlobalScalar X r).naturality g.hom).symm)
      exact mappingCone_map_quasiIso _ _ _ _ _)

/-- The same literal scalar cone in the original relative-acyclic category. -/
def perfectOpenScalarConeFunctor :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⥤
      AcyclicCategory (perfectOpenNested j) :=
  perfectSupportedScalarConeFunctor j r q hq ⋙ perfectSupportedToAcyclic j

/-- The underlying perfect functor is literally the original signed scalar cone. -/
theorem perfectOpenScalarConeFunctor_comp_inclusion :
    perfectOpenScalarConeFunctor j r q hq ⋙ acyclicInclusion (perfectOpenNested j) =
      perfectScalarConeFunctor X r := rfl

/-- Both actual presentations of the supported scalar cone use the fine weak equivalences. -/
theorem perfectOpenScalarConeFunctor_waldhausenExact :
    IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (acyclicStructure (perfectOpenNested j)).cof
      (acyclicStructure (perfectOpenNested j)).weq
      (perfectOpenScalarConeFunctor j r q hq) :=
  (perfectSupportedScalarConeFunctor_waldhausenExact j r q hq).comp
    (perfectSupportedToAcyclic_exact j)

end AlgebraicGeometry.Scheme.Modules
