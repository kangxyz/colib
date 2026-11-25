/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassLaurentBottomFace
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassCommonChartSimplex

/-!
# The fixed common reference of the original Bass bottom family

The common chart map retains the two actual Laurent naturality squares
and the positive projection equation. Every original bottom vertex keeps
its dependent reference isomorphism. Adapted from
`BassBottomCommonFamily.lean` in the original BoundedFlat proof at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassBottomCommonFamily

open BoundedFlatCoefficientBassOverlap

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Laurent naturality and the actual positive projection equation identify the bottom total. -/
theorem bottom_total :
    (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v ≫
      BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u) ≫
      (laurentPlus P a ≫ polynomialProjection P a) =
        laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  rw [laurentPlus_projection]
  simp only [Category.assoc]
  rw [laurentProjection_naturality P u, ← Category.assoc _ _ (coefficientMap P u),
    laurentProjection_naturality P v]
  simp only [Category.assoc]

/-- The bottom grid's reference uses the same actual total as both chart families. -/
def referenceIso : (BoundedFlatCoefficientBassOverlap.commonReference P u v).hom.toFunctor ≅
    (BoundedFlatCoefficientBassProjectionPath.source P a ≫
      BoundedFlatCoefficientBassLaurentBottomFace.source P u v).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback (bottom_total P u v).symm) ≪≫
      boundedAboveFlatPerfectNormalizedPullbackCompIso
        (BoundedFlatCoefficientBassLaurentBottomFace.firstMap P v ≫
      BoundedFlatCoefficientBassLaurentBottomFace.secondMap P u)
        (laurentPlus P a ≫ polynomialProjection P a)) AsSmall.up)

/-- The whole bottom diagram retains all product references after changing the common anchor. -/
def bottomNodes (i : Fin 15) : BoundedFlatCoefficientBassOverlap.Node P u v :=
  ⟨CommonReferenceProduct.vertices
      (fun j ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a j).1)
      (BoundedFlatCoefficientBassLaurentBottomFace.vertices P u v) i,
    referenceIso P u v ≪≫ CommonReferenceProduct.references
      (BoundedFlatCoefficientBassProjectionPath.source P a)
      (fun j ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a j).1)
      (fun j ↦ (BoundedFlatCoefficientBassProjectionPath.nodes P a j).2)
      (BoundedFlatCoefficientBassLaurentBottomFace.source P u v)
      (BoundedFlatCoefficientBassLaurentBottomFace.vertices P u v)
      (BoundedFlatCoefficientBassLaurentBottomFace.references P u v) i⟩

/-- Changing the reference recovers the entire unchanged Laurent bottom simplex. -/
theorem bottom_reference : ModelSimplex.ofIsos
    (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (fun i ↦ (bottomNodes P u v i).1) (fun i ↦ (bottomNodes P u v i).2) =
    BoundedFlatCoefficientBassLaurentBottomFace.simplex P u v :=
  ModelSimplex.ofIsos_change_reference (referenceIso P u v) _ _

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassBottomCommonFamily
