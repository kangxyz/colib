/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Diagram

/-!
# Exact outer-node normal forms of the Bass H0 family

These are full reference nodes, not just underlying functors. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/H0OuterReferenceNodes.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1H0Boundary
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)

theorem laurent_naturality : coefficientMap P ((laurentUnderFunctor R).map w) ≫
    laurentProjection P a = laurentProjection P b ≫ coefficientMap P w :=
  laurentProjection_naturality P w

/-- The positions of the five shared outer-path nodes in the combined 31-vertex H0 diagram. -/
def outerIndex (i : Fin 5) : Fin 31 :=
  BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
    (BoundedFlatPerfectProjectionReference.sharedIndex i)

/-- Original H0 outer nodes use the actual Laurent square, independent of chart factorization. -/
theorem outer_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH0Diagram.nodes P w (outerIndex i) =
      BoundedFlatPerfectProjectionReference.outerNodes (coefficientMap P w)
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (laurentProjection P a) (laurentProjection P b) (laurent_naturality P w) i :=
  (BoundedFlatCoefficientBassH0Diagram.plus_nodes P w
    (BoundedFlatPerfectProjectionReference.sharedIndex i)).trans
    (BoundedFlatPerfectProjectionReference.shared_nodes
      (polynomialProjection P a) (laurentPlus P a)
      (polynomialProjection P b) (laurentPlus P b)
      (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
      (coefficientMap P ((laurentUnderFunctor R).map w))
      (polynomialProjection_naturality P w)
      (coefficientMap_naturality_of_natTrans P (underToLaurent R) w)
      (laurentProjection P a) (laurentProjection P b)
      (laurentPlus_projection P a) (laurentPlus_projection P b) i)

/-- The complete original normalized source node, with its original binary reference. -/
theorem source_normal : BoundedFlatCoefficientBassH0Diagram.nodes P w 2 =
    (⟨BoundedFlatPerfectBinarySimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a),
      BoundedFlatPerfectBinarySimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map w)) (laurentProjection P a)⟩ :
      BoundedFlatCoefficientBassH0Diagram.Node P w) :=
  outer_nodes P w 2

/-- The original full target node retains its actual Laurent naturality source transport. -/
theorem target_normal : BoundedFlatCoefficientBassH0Diagram.nodes P w 26 =
    (⟨BoundedFlatPerfectBinarySimplex.targetMap (laurentProjection P b) (coefficientMap P w),
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg boundedAboveFlatPerfectNormalizedPullback (laurent_naturality P w))) ≪≫
        BoundedFlatPerfectBinarySimplex.total (laurentProjection P b) (coefficientMap P w)⟩ :
      BoundedFlatCoefficientBassH0Diagram.Node P w) :=
  outer_nodes P w 4

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1H0Boundary
