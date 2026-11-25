/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTerminalNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitRows

/-! The actual positive and inverse eight-node top families of the original raw identity,
retaining their full references through the corresponding initial middle product nodes.
Adapted from `CoefficientPolynomialSpanUnitNodes.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No complete top or cube is asserted. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
  CategoryTheory.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTopCharts

open BoundedFlatPerfectOriginalUnitSquareSimplex

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "bottomSrc" => BoundedFlatCoefficientBassUnitBottom.source
local notation "unitMiddleNodes" => BoundedFlatCoefficientBassUnitTopMiddle.nodes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- A full original unit node anchored at the base identity followed by the Bass projection. -/
abbrev Node := Σ F : asSmallCategory (W (space (op P, a))) ⟶
    asSmallCategory (W (space (op P, (laurentUnderFunctor R).obj a))),
    (bottomSrc P a).hom.toFunctor ≅ F.hom.toFunctor

/-- The positive square changes reference through its actual shared initial identity node. -/
def plusSourceIso : (bottomSrc P a).hom.toFunctor ≅
    (sourceMap (polynomialProjection P a) ≫ sourceMap (laurentPlus P a)).hom.toFunctor :=
  (unitMiddleNodes P a 2).2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).hom.toFunctor).symm

/-- The negative square uses the actual inverse-chart node, including its source transport. -/
def minusSourceIso : (bottomSrc P a).hom.toFunctor ≅
    (sourceMap (polynomialProjection P a) ≫ sourceMap (laurentMinus P a)).hom.toFunctor :=
  (unitMiddleNodes P a 4).2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).hom.toFunctor).symm

/-- Every positive vertex and its original reference, whiskered by the positive chart. -/
def plusNodes (i : Fin 8) : Node P a :=
  ⟨vertices (polynomialProjection P a) i ≫ sourceMap (laurentPlus P a),
    plusSourceIso P a ≪≫ isoWhiskerRight (references (polynomialProjection P a) i)
      (sourceMap (laurentPlus P a)).hom.toFunctor⟩

/-- Every negative vertex and its original reference, whiskered by the negative chart. -/
def minusNodes (i : Fin 8) : Node P a :=
  ⟨vertices (polynomialProjection P a) i ≫ sourceMap (laurentMinus P a),
    minusSourceIso P a ≪≫ isoWhiskerRight (references (polynomialProjection P a) i)
      (sourceMap (laurentMinus P a)).hom.toFunctor⟩

theorem plus_five : plusNodes P a 5 = unitMiddleNodes P a 2 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (((unitMiddleNodes P a 2).2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).hom.toFunctor).symm) ≪≫
    isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentPlus P a)).hom.toFunctor).hom = (unitMiddleNodes P a 2).2.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem minus_five : minusNodes P a 5 = unitMiddleNodes P a 4 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (((unitMiddleNodes P a 4).2 ≪≫
    (isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).hom.toFunctor).symm) ≪≫
    isoWhiskerRight (leftFirst (polynomialProjection P a))
      (sourceMap (laurentMinus P a)).hom.toFunctor).hom = (unitMiddleNodes P a 4).2.hom
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual positive top simplex on the original eight full nodes. -/
def plusSimplex := ModelSimplex.ofIsos (bottomSrc P a)
  (fun i ↦ (plusNodes P a i).1) (fun i ↦ (plusNodes P a i).2)

/-- The actual inverse top simplex on its distinct eight full nodes. -/
def minusSimplex := ModelSimplex.ofIsos (bottomSrc P a)
  (fun i ↦ (minusNodes P a i).1) (fun i ↦ (minusNodes P a i).2)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTopCharts
