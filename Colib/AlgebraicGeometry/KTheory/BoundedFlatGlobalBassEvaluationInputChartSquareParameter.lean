/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCommutingParameter
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputChartReference
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCompactAttachment

/-!
# Exact compact chart-naturality squares in the mixed Laurent reference

The eight original commuting-square nodes are strictly precomposed with the polynomial
projection and attached with the actual chart equation and original triple reference transport.
Their compact parameter retains the entire original common-prefix cancellation and three-side
collapse. Every native level and all four full boundary paths keep both original times.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSquareParameter
open GlobalSectionChangeIndex

private theorem compact_square_native
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ W) {k : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
    {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}
    (Q : ParameterSquare p₀ p₁ l m)
    {f₀ g₀ f₁ g₁ : prespectrum V ⟶ prespectrum W}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} (B : H₀.Square H₁ L M)
    (h : SquareLift (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) Q B)
    (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily F
      ((CommonReferenceNerve.parameter F N).comp Q.parameter) n =
        (B.level n).comp ⟨fun z ↦ (z.1.1, (z.1.2, z.2)), by fun_prop⟩ := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex F _ N (r, s)
    (Q.parameter (r, s)) rfl n x).trans ?_
  exact h n r s x

private theorem compact_square_precomp_native
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    (F : V ⟶ W) (J : T ⟶ V) (G : T ⟶ W) (ε : G.hom.toFunctor ≅ (J ≫ F).hom.toFunctor)
    {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
    {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {l : Path a₀ a₁} {m : Path b₀ b₁}
    (Q : ParameterSquare p₀ p₁ l m)
    {f₀ g₀ f₁ g₁ : prespectrum V ⟶ prespectrum W}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} (B : H₀.Square H₁ L M)
    (h : SquareLift (ModelSimplex.ofIsos F (fun i ↦ (N i).1) (fun i ↦ (N i).2)) Q B)
    (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily G
      ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPrecompNode F J G ε)).comp
        ((CommonReferenceNerve.parameter F N).comp Q.parameter)) n =
      (B.level n).comp
        ⟨fun z ↦ (z.1.1, (z.1.2, (prespectrumMap J).map n z.2)), by fun_prop⟩ := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  exact (CommonReferenceNerve.compactPrespectrumFamily_attachPrecomp F J G ε
    ((CommonReferenceNerve.parameter F N).comp Q.parameter) n (r, s) x).trans
      (DFunLike.congr_fun (compact_square_native F N Q B h n)
        ((r, s), (prespectrumMap J).map n x))

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The full mixed reference transport retains the actual strict functor association. -/
def sourceIso : (InputMixedDesc.sourceMap g).hom.toFunctor ≅
    (boundedAboveFlatGlobalSectionModelFunctor.map (projection.app Y).op ≫
      InputCommutingSimplex.sourceMap (laurent.map g) (k.app Y)).hom.toFunctor :=
  InputChartReference.chartSourceIso g k hk ≪≫
    InputTripleNodes.preSourceIso (laurent.map g) (k.app Y) (projection.app Y)

/-- Strict polynomial projection and the specified mixed anchor act on each full node. -/
def attachNode := CommonReferenceNerve.attachPrecompNode
  (InputCommutingSimplex.sourceMap (laurent.map g) (k.app Y))
  (boundedAboveFlatGlobalSectionModelFunctor.map (projection.app Y).op)
  (InputMixedDesc.sourceMap g) (sourceIso g k hk)

/-- All eight original nodes survive with their dependent arrows and full attached anchors. -/
def nodes (i : Fin 8) : CommonReferenceNerve.Node (InputMixedDesc.sourceMap g) :=
  attachNode g k hk (InputCommutingSimplex.nodes (laurent.map g) (k.app Y)
    (k.app X) (polynomial.map g) (k.naturality g) i)

/-- The exact original commuting scalar square in its original common-reference nerve. -/
def commutingParameter :=
  (CommonReferenceNerve.parameter (InputCommutingSimplex.sourceMap (laurent.map g) (k.app Y))
    (InputCommutingSimplex.nodes (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g))).comp InputCommutingParameter.parameter

/-- The compact chart-naturality face uses the unchanged original cancellation parameter. -/
def parameter : C(unitInterval × unitInterval,
    |nerve (Codiscrete (CommonReferenceNerve.Node (InputMixedDesc.sourceMap g)))|) :=
  (CommonReferenceNerve.mapParameter (attachNode g k hk)).comp (commutingParameter g k)

/-- The whole characteristic-map family retains precisely the original eight attached nodes. -/
theorem parameter_eq : parameter g k hk =
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk)).comp
      InputCommutingParameter.parameter := by
  apply ContinuousMap.ext
  intro z
  exact CommonReferenceNerve.mapParameter_parameter (attachNode g k hk)
    (InputCommutingSimplex.nodes (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g)) (InputCommutingParameter.parameter z)

/-- The entire native square is unchanged at the strict polynomial-projection input. -/
theorem native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g k hk) n =
    ((InputCommutingSquare.square (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g)).level n).comp
      ⟨fun z ↦ (z.1.1, (z.1.2,
        (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map
          (projection.app Y).op)).map n z.2)), by fun_prop⟩ :=
  compact_square_precomp_native
    (InputCommutingSimplex.sourceMap (laurent.map g) (k.app Y))
    (boundedAboveFlatGlobalSectionModelFunctor.map (projection.app Y).op)
    (InputMixedDesc.sourceMap g) (sourceIso g k hk)
    (InputCommutingSimplex.nodes (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g))
    InputCommutingParameter.parameterSquare
    (InputCommutingSquare.square (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g))
    (InputCommutingParameter.native (laurent.map g) (k.app Y)
      (k.app X) (polynomial.map g) (k.naturality g)) n

/-- An original scalar edge in the actual attached eight-node characteristic map. -/
def edge (i j : Fin 8) :=
  (SimplexParameters.edge i j).map
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk)).continuous

/-- The source side is the complete original zero-to-six path, with its original clock. -/
theorem parameter_zero (s : unitInterval) :
    parameter g k hk (0, s) = edge g k hk 0 6 s := by
  rw [parameter_eq]
  exact congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk))
    (InputCommutingParameter.parameter_zero s)

/-- The target side retains the exact reverse-forward composition word and all its clocks. -/
theorem parameter_one (s : unitInterval) :
    parameter g k hk (1, s) =
      ((edge g k hk 3 4).trans
        (((edge g k hk 1 2).trans (edge g k hk 2 4)).symm.trans
          ((edge g k hk 1 5).trans (edge g k hk 5 7)))) s := by
  rw [parameter_eq]
  change CommonReferenceNerve.parameter _ _ (InputCommutingParameter.parameter (1, s)) = _
  rw [InputCommutingParameter.parameter_one]
  change (((SimplexParameters.edge (k := 7) 3 4).trans
    (((SimplexParameters.edge 1 2).trans (SimplexParameters.edge 2 4)).symm.trans
      ((SimplexParameters.edge 1 5).trans (SimplexParameters.edge 5 7)))).map
        (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
          (nodes g k hk)).continuous) s = _
  simp only [Path.map_trans, ← Path.map_symm, edge]

/-- The left side retains the complete original zero-to-three path. -/
theorem parameter_left (r : unitInterval) :
    parameter g k hk (r, 0) = edge g k hk 0 3 r := by
  rw [parameter_eq]
  exact congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk))
    (InputCommutingParameter.parameter_left r)

/-- The right side retains the complete original six-to-seven path. -/
theorem parameter_right (r : unitInterval) :
    parameter g k hk (r, 1) = edge g k hk 6 7 r := by
  rw [parameter_eq]
  exact congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk))
    (InputCommutingParameter.parameter_right r)

/-- The positive chart face uses its actual Laurent projection equation. -/
def plusParameter := parameter g plus GlobalRawBass.plus_projection

/-- The inverse chart face uses its actual Laurent projection equation. -/
def minusParameter := parameter g minus GlobalRawBass.minus_projection

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputChartSquareParameter
