/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Naturality
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.GraphSupport

/-!
# The literal graph cut and the monic Laurent quotient

The zero fiber of a Laurent polynomial times a unit retains the full principal
ideal of the polynomial. Its isomorphism with the original quotient identifies
the maps to the Laurent chart and to the base. After arbitrary base change the
whole fiber has the same finite flat rank.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {k : Type u} [Field k]

/-- The actual global section of the chart determined by a Laurent polynomial. -/
def chartCutSection (a : LaurentPolynomial k) : Γ(Spec (.of (LaurentPolynomial k)), ⊤) :=
  (ΓSpecIso (.of (LaurentPolynomial k))).inv a

/-- The section map to the affine line whose zero fiber is the literal cut. -/
abbrev chartCutParameter (a : LaurentPolynomial k) :
    Spec (.of (LaurentPolynomial k)) ⟶ Spec (.of k[X]) :=
  sectionToAffineLine chartProjection (chartCutSection a)

/-- A Laurent unit preserves the whole principal ideal of the original zero fiber. -/
theorem chartCut_inclusion_ker (p : k[X]) (h₀ : IsUnit (p.coeff 0))
    (a : LaurentPolynomial k) (ha : IsUnit a) :
    (AffineLineFiber.inclusion (chartCutParameter (a * toLaurent p)) 0).ker =
      (chartQuotient p h₀).ker := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [AffineLineFiber.inclusion_ker, Stacks.IdealSheaf.ideal_comap_top_of_isAffine,
    AffineLineFiber.point_ideal, Ideal.map_map, Ideal.map_span, Set.image_singleton,
    map_sub, Polynomial.C_0, map_zero, sub_zero,
    RingHom.comp_apply, sectionToAffineLine_coordinate, chartQuotient_ker_top, chartCutSection,
    map_mul]
  exact Ideal.span_singleton_mul_left_unit (ha.map (ΓSpecIso (.of (LaurentPolynomial k))).inv.hom) _

/-- The literal zero fiber and the monic quotient have the same entire support over the chart. -/
def chartCutIso (p : k[X]) (h₀ : IsUnit (p.coeff 0)) (a : LaurentPolynomial k) (ha : IsUnit a) :
    AffineLineFiber.fiber (chartCutParameter (a * toLaurent p)) 0 ≅ Spec (.of (AdjoinRoot p)) := by
  let e := IsClosedImmersion.lift (chartQuotient p h₀)
    (AffineLineFiber.inclusion (chartCutParameter (a * toLaurent p)) 0)
    (chartCut_inclusion_ker p h₀ a ha).ge
  letI : IsIso e := IsClosedImmersion.isIso_lift _ _ (chartCut_inclusion_ker p h₀ a ha).symm
  exact asIso e

@[reassoc]
theorem chartCutIso_hom_chartQuotient (p : k[X]) (h₀ : IsUnit (p.coeff 0))
    (a : LaurentPolynomial k) (ha : IsUnit a) :
    (chartCutIso p h₀ a ha).hom ≫ chartQuotient p h₀ =
      AffineLineFiber.inclusion (chartCutParameter (a * toLaurent p)) 0 :=
  IsClosedImmersion.lift_fac _ _ _

variable {P D : Scheme.{u}} {q : P ⟶ Spec (.of k)} {π : D ⟶ P}
  {v : D ⟶ Spec (.of (LaurentPolynomial k))}

/-- The chart equation pulled back to the original support defines the same section map. -/
theorem chartCutParameter_baseChange (H : IsPullback v π chartProjection q)
    (a : LaurentPolynomial k) :
    sectionToAffineLine (π ≫ q) (v.appTop (chartCutSection a)) = v ≫ chartCutParameter a := by
  rw [← H.w, sectionToAffineLine_comp]

/-- The entire zero fiber over the graph is the base change of the Laurent quotient. -/
theorem chartCutBaseChange_isPullback (H : IsPullback v π chartProjection q)
    (p : k[X]) (h₀ : IsUnit (p.coeff 0)) (a : LaurentPolynomial k) (ha : IsUnit a) :
    IsPullback
      (AffineLineFiber.fiberMap (chartCutParameter (a * toLaurent p)) 0 v ≫
        (chartCutIso p h₀ a ha).hom)
      (AffineLineFiber.inclusion (v ≫ chartCutParameter (a * toLaurent p)) 0 ≫ π)
      (projection p) q := by
  let f := chartCutParameter (a * toLaurent p)
  have h := (AffineLineFiber.fiberMap_isPullback f 0 v).paste_vert H
  refine h.of_iso (Iso.refl _) (chartCutIso p h₀ a ha) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [f]
  · simp [f]
  · rw [Iso.refl_hom, Category.comp_id, ← chartQuotient_projection p h₀,
      chartCutIso_hom_chartQuotient_assoc]
  · simp

/-- The map from the whole cut to the original support is finite for a monic equation. -/
theorem chartCutBaseChange_isFinite (H : IsPullback v π chartProjection q)
    (p : k[X]) (hp : p.Monic) (h₀ : IsUnit (p.coeff 0))
    (a : LaurentPolynomial k) (ha : IsUnit a) :
    IsFinite (AffineLineFiber.inclusion (v ≫ chartCutParameter (a * toLaurent p)) 0 ≫ π) := by
  let := projection_isFinite p hp
  exact MorphismProperty.of_isPullback (chartCutBaseChange_isPullback H p h₀ a ha)
    inferInstance

/-- The finite pushforward of the actual zero fiber is its monic rank times the
original whole support pushforward. -/
theorem finiteCyclePushforward_chartCutBaseChange [IsNoetherian P] {Z : Scheme.{u}}
    (j : P ⟶ Z) [IsFinite j] (H : IsPullback v π chartProjection q)
    (p : k[X]) (hp : p.Monic) (h₀ : IsUnit (p.coeff 0))
    (a : LaurentPolynomial k) (ha : IsUnit a) :
    let f := v ≫ chartCutParameter (a * toLaurent p)
    letI : IsFinite (AffineLineFiber.inclusion f 0 ≫ π) :=
      chartCutBaseChange_isFinite H p hp h₀ a ha
    letI : IsNoetherian (AffineLineFiber.fiber f 0) :=
      isNoetherian_of_finiteType (AffineLineFiber.inclusion f 0 ≫ π)
    finiteCyclePushforward ((AffineLineFiber.inclusion f 0 ≫ π) ≫ j)
        (AlgebraicCycle.fundamentalCycle (AffineLineFiber.fiber f 0)) =
      (p.natDegree : ℤ) • finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle P) := by
  let f := v ≫ chartCutParameter (a * toLaurent p)
  let : IsFinite (AffineLineFiber.inclusion f 0 ≫ π) := chartCutBaseChange_isFinite H p hp h₀ a ha
  let : IsNoetherian (AffineLineFiber.fiber f 0) :=
    isNoetherian_of_finiteType (AffineLineFiber.inclusion f 0 ≫ π)
  let : IsFinite (projection p) := projection_isFinite p hp
  let : IsNoetherian (pullback q (projection p)) :=
    isNoetherian_of_finiteType (pullback.fst q (projection p))
  let h := (chartCutBaseChange_isPullback H p h₀ a ha).flip
  let e := h.isoPullback
  have he := finiteCyclePushforward_comp_apply e.hom (pullback.fst q (projection p) ≫ j)
    (AlgebraicCycle.fundamentalCycle (AffineLineFiber.fiber f 0))
  rw [finiteCyclePushforward_fundamentalCycle_iso e] at he
  refine (finiteCyclePushforward_congr _ _ ?_ _).trans
    (he.symm.trans (finiteCyclePushforward_polynomialSupport j q p hp))
  rw [← Category.assoc, h.isoPullback_hom_fst]

end AlgebraicGeometry.NativeTorusPolynomial
