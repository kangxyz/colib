/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitHZeroNodes

/-!
# Full identity transport for the two raw Bass charts

Keep the original chart normalization rectangles and every reference isomorphism when
specializing the coefficient homomorphism to the identity. Adapted from
`CoefficientBassUnitHZeroNodes.lean` at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
No chart is identified with a top or bottom face here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitHZeroNodes

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "binaryModelSourceMap" => BoundedFlatPerfectBinarySimplex.sourceMap
local notation "projectionRefNodes" => BoundedFlatPerfectProjectionReference.nodes
local notation "projectionRefReference" => BoundedFlatPerfectProjectionReference.reference
local notation "hZeroChartNodes" => BoundedFlatCoefficientBassH0Diagram.chartNodes
local notation "bottomSrc" => BoundedFlatCoefficientBassUnitBottom.source
local notation "bottomToProj" => BoundedFlatCoefficientBassUnitBottom.sourceToProjection
local notation "bassProjSource" => BoundedFlatCoefficientBassProjectionPath.source

section Rectangle

variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y)

/-- The literal identity rectangle retains its original projection source after normalization. -/
theorem rectangleSourceEq : (binaryModelSourceMap q p).hom.toFunctor =
    (projectionRefReference (𝟙 Z) (q ≫ p)).hom.toFunctor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.id_comp (q ≫ p)).symm)

variable (F : asSmallCategory (W X) ⟶ asSmallCategory (W Z))
  (δ : F.hom.toFunctor ≅ (binaryModelSourceMap q p).hom.toFunctor)

/-- The entire identity rectangle with its original chart anchor and all dependent nodes. -/
def rectangleNodes (i : Fin 18) :
    Σ G : asSmallCategory (W X) ⟶ asSmallCategory (W Z),
      F.hom.toFunctor ≅ G.hom.toFunctor :=
  ModelSimplex.reanchorNode (δ ≪≫ eqToIso (rectangleSourceEq p q))
    (projectionRefNodes p q p q (𝟙 X) (𝟙 Y) (𝟙 Z) (by simp) (by simp) (q ≫ p) rfl i)

end Rectangle

/-- Transporting the three geometric identity equalities preserves every entire dependent node. -/
private theorem rectangle_identity_transport {X Y Z : Scheme.{u}}
    (p : Y ⟶ X) (q : Z ⟶ Y) (a₀ : X ⟶ X) (b₀ : Y ⟶ Y) (c₀ : Z ⟶ Z)
    (ha₀ : a₀ = 𝟙 X) (hb₀ : b₀ = 𝟙 Y) (hc₀ : c₀ = 𝟙 Z)
    (hp : b₀ ≫ p = p ≫ a₀) (hq : c₀ ≫ q = q ≫ b₀)
    (r : Z ⟶ X) (hr : q ≫ p = r)
    (F G : asSmallCategory (W X) ⟶ asSmallCategory (W Z)) (ρ : F.hom.toFunctor ≅ G.hom.toFunctor)
    (e : G.hom.toFunctor = (projectionRefReference c₀ r).hom.toFunctor)
    (d : G.hom.toFunctor = (binaryModelSourceMap q p).hom.toFunctor) (i : Fin 18) :
    ModelSimplex.reanchorNode (ρ ≪≫ eqToIso e)
        (projectionRefNodes p q p q a₀ b₀ c₀ hp hq r hr i) =
      rectangleNodes p q F (ρ ≪≫ eqToIso d) i := by
  subst a₀
  subst b₀
  subst c₀
  subst r
  unfold rectangleNodes
  rw [Iso.trans_assoc, eqToIso_trans]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The common projection and the actual chart factorization normalize to the same functor. -/
theorem chartProjectionEq
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    (bassProjSource P a).hom.toFunctor =
    (binaryModelSourceMap (coefficientMap P (α.app a)) (polynomialProjection P a)).hom.toFunctor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback
      ((laurentPlus_projection P a).trans ha.symm))

variable (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- Retain the exact signed chart factorization under the canonical raw identity anchor. -/
def chartProjectionIso : (bottomSrc P a).hom.toFunctor ≅
    (binaryModelSourceMap (coefficientMap P (α.app a)) (polynomialProjection P a)).hom.toFunctor :=
  bottomToProj P a ≪≫ eqToIso (chartProjectionEq P a α ha)

/-- Every original chart rectangle is reanchored through the same H₀ identity source. -/
def chartNodes (i : Fin 18) :=
  ModelSimplex.reanchorNode (h0SourceIso P a) (hZeroChartNodes P (𝟙 a) α ha i)

/-- The original coefficient identity preserves all 18 full nodes of the native chart. -/
theorem chart_identity (i : Fin 18) : chartNodes P a α ha i =
    rectangleNodes (polynomialProjection P a) (coefficientMap P (α.app a))
      (bottomSrc P a) (chartProjectionIso P a α ha) i := by
  have h :=
    rectangle_identity_transport (polynomialProjection P a) (coefficientMap P (α.app a))
      (coefficientMap P (𝟙 a)) (coefficientMap P ((polynomialUnderFunctor R).map (𝟙 a)))
      (coefficientMap P ((laurentUnderFunctor R).map (𝟙 a)))
      (boundedAboveFlatCoefficientGeometricIdentity P a)
      ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_id a)).trans
        (boundedAboveFlatCoefficientGeometricIdentity P _))
      ((congrArg (coefficientMap P) ((laurentUnderFunctor R).map_id a)).trans
        (boundedAboveFlatCoefficientGeometricIdentity P _))
      (polynomialProjection_naturality P (𝟙 a))
      (coefficientMap_naturality_of_natTrans P α (𝟙 a))
      (laurentProjection P a) ha
      (bottomSrc P a) (bassProjSource P a) (bottomToProj P a)
      (h0SourceEq P a) (chartProjectionEq P a α ha) i
  exact h

/-- The positive chart uses its literal Laurent factorization. -/
theorem plus_chart_identity (i : Fin 18) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a) i =
      rectangleNodes (polynomialProjection P a) (laurentPlus P a)
        (bottomSrc P a)
        (chartProjectionIso P a (underToLaurent R) (laurentPlus_projection P a)) i :=
  chart_identity P a (underToLaurent R) (laurentPlus_projection P a) i

/-- The inverse chart uses its own literal Laurent factorization and the same canonical anchor. -/
theorem minus_chart_identity (i : Fin 18) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a) i =
      rectangleNodes (polynomialProjection P a) (laurentMinus P a)
        (bottomSrc P a)
        (chartProjectionIso P a (underToLaurentInvert R) (laurentMinus_projection P a)) i :=
  chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) i

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitHZeroNodes
