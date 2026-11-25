/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputDescNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumIdentitySimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitChartSideRows

/-!
# The actual H₀ identity surface and its full normalized reference nodes

The original global unit anchor reanchors the whole thirty-one-node input rectangle.
Both Laurent chart restrictions and all cylinder coordinates are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityNodes

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
open ModelSimplex (reanchorNode)
open BoundedFlatPerfectProjectionBinaryRows (rightIndex)
open BoundedFlatCoefficientBassUnitHZeroNodes
  (rectangleNodes rectangleSideNodes rectangle_side_right rectangle_side_left)

private theorem rectangle_identity_transport {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (a₀ : A ⟶ A) (b₀ : B ⟶ B) (c₀ : C ⟶ C)
    (ha₀ : a₀ = 𝟙 A) (hb₀ : b₀ = 𝟙 B) (hc₀ : c₀ = 𝟙 C)
    (hp : b₀ ≫ p = p ≫ a₀) (hq : c₀ ≫ q = q ≫ b₀)
    (r : C ⟶ A) (hr : q ≫ p = r)
    (F G : asSmallCategory (W A) ⟶
      asSmallCategory (W C)) (ρ : F.hom.toFunctor ≅ G.hom.toFunctor)
    (e : G.hom.toFunctor = (BoundedFlatPerfectProjectionReference.reference c₀ r).hom.toFunctor)
    (d : G.hom.toFunctor = (BoundedFlatPerfectBinarySimplex.sourceMap q p).hom.toFunctor) :
    (fun i ↦ reanchorNode (ρ ≪≫ eqToIso e)
      (BoundedFlatPerfectProjectionReference.nodes p q p q a₀ b₀ c₀ hp hq r hr i)) =
      rectangleNodes p q F (ρ ≪≫ eqToIso d) := by
  subst a₀
  subst b₀
  subst c₀
  subst r
  unfold rectangleNodes
  rw [Iso.trans_assoc, eqToIso_trans]

variable (X : Scheme.{u})

/-- The original positive binary source is the common geometric Laurent projection. -/
abbrev projectionSource :=
  BoundedFlatPerfectBinarySimplex.sourceMap (plus.app X) (projection.app X)

/-- The original base identity and projection supply the unchanged product reference. -/
abbrev source := BoundedFlatPerfectIdentitySimplex.source X ≫ projectionSource X

/-- Each node includes its entire isomorphism from the actual product reference. -/
abbrev Node := Σ F : asSmallCategory (W X) ⟶
    asSmallCategory (W (laurent.obj X)), (source X).hom.toFunctor ≅ F.hom.toFunctor

/-- The split original base unit supplies the actual projection reference isomorphism. -/
def sourceToProjection : (source X).hom.toFunctor ≅ (projectionSource X).hom.toFunctor :=
  isoWhiskerRight (BoundedFlatPerfectIdentitySimplex.first X ≪≫
    BoundedFlatPerfectIdentitySimplex.second X) (projectionSource X).hom.toFunctor

/-- The real Laurent functor identity identifies the unchanged input reference. -/
theorem inputSourceEq : (projectionSource X).hom.toFunctor =
    (InputDescSimplex.reference (𝟙 X)).hom.toFunctor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (by
      rw [laurent.map_id, Category.id_comp]
      exact plus_projection X))

/-- All original input vertices use this same actual base-unit reference transport. -/
def inputSourceIso : (source X).hom.toFunctor ≅ (InputDescSimplex.reference (𝟙 X)).hom.toFunctor :=
  sourceToProjection X ≪≫ eqToIso (inputSourceEq X)

/-- The thirty-one original input nodes retain every geometric map and reference. -/
def nodes (i : Fin 31) : Node X :=
  reanchorNode (inputSourceIso X) (InputDescSimplex.nodes (𝟙 X) i)

/-- The actual original input simplex with its product reference, before any scalar evaluation. -/
def simplex : ModelSimplex (asSmallCategory (W X))
    (asSmallCategory (W (laurent.obj X))) 30 :=
  ModelSimplex.reanchorSimplex (F₀ := source X) (F₁ := InputDescSimplex.reference (𝟙 X))
    (inputSourceIso X) (InputDescSimplex.nodes (𝟙 X))

/-- Reanchoring retains the complete original input Model simplex. -/
theorem simplex_original : simplex X = InputDescSimplex.simplex (𝟙 X) :=
  ModelSimplex.reanchorSimplex_eq (F₀ := source X) (F₁ := InputDescSimplex.reference (𝟙 X))
    (inputSourceIso X) (InputDescSimplex.nodes (𝟙 X))

variable (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = laurentProjection.app Z)

include hk in
/-- The genuine positive/inverse projection equation identifies the binary chart reference. -/
theorem chartProjectionEq : (projectionSource X).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap (k.app X) (projection.app X)).hom.toFunctor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback ((plus_projection X).trans (hk X).symm))

/-- The chart reference retains both original base-unit steps and its projection equation. -/
def chartProjectionIso : (source X).hom.toFunctor ≅
    (BoundedFlatPerfectBinarySimplex.sourceMap (k.app X) (projection.app X)).hom.toFunctor :=
  sourceToProjection X ≪≫ eqToIso (chartProjectionEq X k hk)

/-- Every original eighteen-node chart is retained with the common original input anchor. -/
def chartNodes (i : Fin 18) : Node X :=
  reanchorNode (inputSourceIso X) (InputDescSimplex.chartNodes (𝟙 X) k hk i)

/-- Identity-arrow transport preserves the entire family of dependent geometric chart nodes. -/
theorem chart_identity_family : chartNodes X k hk =
    rectangleNodes (projection.app X) (k.app X) (source X) (chartProjectionIso X k hk) :=
  rectangle_identity_transport (projection.app X) (k.app X)
    (𝟙 X) (polynomial.map (𝟙 X)) (laurent.map (𝟙 X))
    rfl (polynomial.map_id X) (laurent.map_id X)
    (projection.naturality (𝟙 X)) (k.naturality (𝟙 X))
    (laurentProjection.app X) (hk X) (source X) (projectionSource X)
    (sourceToProjection X) (inputSourceEq X) (chartProjectionEq X k hk)

/-- Each chart node keeps its original map and complete identity-rectangle anchor. -/
theorem chart_identity (i : Fin 18) : chartNodes X k hk i =
    rectangleNodes (projection.app X) (k.app X) (source X) (chartProjectionIso X k hk) i :=
  congrFun (chart_identity_family X k hk) i

/-- The full unit-side nodes retain actual polynomial precomposition and both unit routes. -/
def chartSideNodes (i : Fin 8) : Node X :=
  rectangleSideNodes (projection.app X) (k.app X) (source X) (chartProjectionIso X k hk) i

/-- The initial three-node chart row is the first original unit-square row, including anchors. -/
theorem chart_unit_right (i : Fin 3) :
    chartNodes X k hk
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      chartSideNodes X k hk (![0, 1, 2] i) :=
  (chart_identity X k hk _).trans
    (rectangle_side_right (projection.app X) (k.app X) (source X)
      (chartProjectionIso X k hk) i)

/-- The other three-node chart row keeps the second original unit-square route separately. -/
theorem chart_unit_left (i : Fin 3) :
    chartNodes X k hk
      (BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      chartSideNodes X k hk (![0, 4, 5] i) :=
  (chart_identity X k hk _).trans
    (rectangle_side_left (projection.app X) (k.app X) (source X)
      (chartProjectionIso X k hk) i)

/-- All eighteen positive nodes sit in the unchanged thirty-one-node input surface. -/
theorem plus_nodes (i : Fin 18) :
    nodes X (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom i) =
      chartNodes X plus plus_projection i :=
  congrArg (reanchorNode (inputSourceIso X)) (InputDescSimplex.plus_nodes (𝟙 X) i)

/-- All eighteen inverse nodes retain their separate maps and the five genuine shared anchors. -/
theorem minus_nodes (i : Fin 18) :
    nodes X (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom i) =
      chartNodes X minus minus_projection i :=
  congrArg (reanchorNode (inputSourceIso X)) (InputDescSimplex.minus_nodes (𝟙 X) i)

/-- Both original comparison times survive the full identity-reference transport. -/
theorem cylinder_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W X)).space n) :
    prespectrumSimplexFamily (simplex X) n
      (BoundedFlatCoefficientBassH0Diagram.parameter (r, s), x) =
      (inputComparisonHomotopy (𝟙 X)).level n
        (r, HomotopyPushout.cylinder
          (K (projection.app X))
          (K (projection.app X)) n (s, x)) := by
  rw [simplex_original]
  exact InputDescSimplex.cylinder_native (𝟙 X) n r s x

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityNodes
