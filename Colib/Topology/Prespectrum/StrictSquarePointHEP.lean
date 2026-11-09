/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.StrictSquareCone
public import Colib.Topology.Prespectrum.StrictSquareSeparation
public import Colib.Topology.Prespectrum.PushoutReduction
public import Colib.Topology.HomotopyCofiber.ReducedMappingConeCollapse
public import Colib.Topology.Prespectrum.ParameterLoopingPointHEP

/-!
# Point HEP of the actual strict-square Bass value

The actual reduced double cylinder, cone and compact-open loop retain HEP of their
literal chosen points. Existing native T1 instances supply separation where required.
The assertions include level zero, with no inference from T1 separation to point HEP.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StrictSquareTopology.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable (S : Arrow (Arrow LoopPrespectrum.{u})) (n : ℕ)

/-- The actual chosen span point has HEP whenever the three original corner points do. -/
theorem span_point_homotopyExtensionProperty
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.left.point n))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.right.point n))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.left.point n)))) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((span S).point n))) :=
  HomotopyPushout.point_homotopyExtensionProperty S.left.hom S.hom.left n hA hB hC

/-- The literal cone point inherits the four genuine point-extension properties. -/
theorem cone_point_homotopyExtensionProperty
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.left.point n))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.right.point n))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.left.point n))))
    (hD : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.right.point n)))) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1}
      ((mappingCone (comparison S)).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty
    ((span S).point n) (S.right.right.point n) ((comparison S).map n)
    ((comparison S).map_point n) (span_point_homotopyExtensionProperty S n hA hB hC) hD

/-- Closed original points with HEP remain well-based in the actual looped cone. -/
theorem loopedCone_point_homotopyExtensionProperty
    [T1Space (S.left.left.space n)] [T1Space (S.left.right.space n)]
    [T1Space (S.right.left.space n)] [T1Space (S.right.right.space n)]
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.left.point n))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.right.point n))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.left.point n))))
    (hD : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.right.point n)))) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1}
      ((strictSquareLoopedConeFunctor.obj S).point n))) :=
  parameterLooping_point_homotopyExtensionProperty (mappingCone (comparison S)) n
    isClosed_singleton (cone_point_homotopyExtensionProperty S n hA hB hC hD)

end Topology.LoopPrespectrum.StrictSquare

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/StrictSquareTopology.lean:43"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.StrictSquare.span_point_homotopyExtensionProperty

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/StrictSquareTopology.lean:55"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.StrictSquare.cone_point_homotopyExtensionProperty

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/StrictSquareTopology.lean:71"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.StrictSquare.loopedCone_point_homotopyExtensionProperty
