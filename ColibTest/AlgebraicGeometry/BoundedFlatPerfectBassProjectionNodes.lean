import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectBassProjectionNodes

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Modules.BassProjectionNodes

universe u

example (X : Scheme.{u}) :
    (nodes X (plusFace.toOrderHom 2)).1 = map (projection.app X) ≫ map (plus.app X) := rfl

example (X : Scheme.{u}) :
    (nodes X (minusFace.toOrderHom 2)).1 = map (projection.app X) ≫ map (minus.app X) := rfl

example (X : Scheme.{u}) :
    (nodes X (minusFace.toOrderHom 1)).2 =
      sourceIso X ≪≫ first (minus.app X) (projection.app X) := rfl

#print axioms AlgebraicGeometry.Scheme.Modules.BassProjectionNodes.nodes
