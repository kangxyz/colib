/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiScalar

/-! # Original outer-cell formulas for the geometric comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
universe u v w
namespace KTheory.Bass.GeometricChiCell
open GeometricSquareInterchange SquareConeStrength
open PushoutStrength PushoutCofiberSquare WholeSeedCospan
open GeometricChiPermutation

section General
variable {C : Type u} [Category.{v} C]
  (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))) (Q : C ⥤ Arrow (Arrow C))
  {T : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))} (e : T ⟶ bassSquare S Q)
  (X : C) (n : ℕ)

/-- The actual upper cylinder is transported at the unchanged cone height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiCell.lean:32"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem chiAlong_upper (r : unitInterval) (x : (T.left.right.obj X).space n) :
    ((chiAlong S Q e).app X).map n (Cell.upper ((squareDiagram T).obj X) n r x) =
      (((strictDiagramFunctor Q).map
        (left S.left.hom S.hom.left ≫
          diagramHomotopyAt (coneNull (comparison S))
            (coneNull_naturality (comparison S)) r)).app X).map n
        ((e.left.right.app X).map n x) := by
  change ((chi S Q).app X).map n
    ((mappingConeHomotopy ((comparison (bassSquare S Q)).app X)).level n
      (r, HomotopyPushout.left _ _ n ((e.left.right.app X).map n x))) = _
  rw [chi_cylinder]
  change ((((strictDiagramFunctor Q).map (left S.left.hom S.hom.left) ≫
    (strictDiagramFunctor Q).map (diagramHomotopyAt (coneNull (comparison S))
      (coneNull_naturality (comparison S)) r)).app X).map n
        ((e.left.right.app X).map n x)) = _
  rw [← Functor.map_comp]

/-- The actual lower cylinder is transported at the unchanged cone height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiCell.lean:50"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem chiAlong_lower (r : unitInterval) (x : (T.right.left.obj X).space n) :
    ((chiAlong S Q e).app X).map n (Cell.lower ((squareDiagram T).obj X) n r x) =
      (((strictDiagramFunctor Q).map
        (right S.left.hom S.hom.left ≫
          diagramHomotopyAt (coneNull (comparison S))
            (coneNull_naturality (comparison S)) r)).app X).map n
        ((e.right.left.app X).map n x) := by
  change ((chi S Q).app X).map n
    ((mappingConeHomotopy ((comparison (bassSquare S Q)).app X)).level n
      (r, HomotopyPushout.right _ _ n ((e.right.left.app X).map n x))) = _
  rw [chi_cylinder]
  change ((((strictDiagramFunctor Q).map (right S.left.hom S.hom.left) ≫
    (strictDiagramFunctor Q).map (diagramHomotopyAt (coneNull (comparison S))
      (coneNull_naturality (comparison S)) r)).app X).map n
        ((e.right.left.app X).map n x)) = _
  rw [← Functor.map_comp]

/-- Both independent original cylinder parameters survive the actual comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricChiCell.lean:68"
  "adaptation" "Original whole geometric chi comparison via the actual cone cells."]
theorem chiAlong_overlap (r s : unitInterval) (x : (T.left.left.obj X).space n) :
    ((chiAlong S Q e).app X).map n (Cell.overlap ((squareDiagram T).obj X) n r s x) =
      (((strictDiagramFunctor Q).map
        (diagramHomotopyAt (glue S.left.hom S.hom.left)
          (glue_naturality S.left.hom S.hom.left) s ≫
          diagramHomotopyAt (coneNull (comparison S))
            (coneNull_naturality (comparison S)) r)).app X).map n
        ((e.left.left.app X).map n x) := by
  change ((chi S Q).app X).map n
    ((mappingConeHomotopy ((comparison (bassSquare S Q)).app X)).level n
      (r, HomotopyPushout.cylinder _ _ n (s, (e.left.left.app X).map n x))) = _
  rw [chi_cylinder]
  change (((strictDiagramFunctor Q).map
    (diagramHomotopyAt (coneNull (comparison S))
      (coneNull_naturality (comparison S)) r)).app X).map n
        (((strictDiagramMapHomotopy (glue S.left.hom S.hom.left)
          (glue_naturality S.left.hom S.hom.left) Q X).at s).map n
            ((e.left.left.app X).map n x)) = _
  rw [strictDiagramMapHomotopy_at]
  exact congrArg (fun a => (a.app X).map n ((e.left.left.app X).map n x))
    ((strictDiagramFunctor Q).map_comp _ _).symm
end General

end KTheory.Bass.GeometricChiCell
