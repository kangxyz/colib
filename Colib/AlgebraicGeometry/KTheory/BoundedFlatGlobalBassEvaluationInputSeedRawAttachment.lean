/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedRawUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanTargetNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedCarrier
public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily

/-!
# Both actual raw-seed attachments in the mixed carrier

The full polynomial source node pins the ordinary reference square. Every original raw
node then satisfies that square by fixed-reference cancellation. The original Laurent-unit
intertwining gives the second square with its distinct shifted attachment.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen SmallWaldhausenCategory AlgebraicGeometry.RingedSpace SSet
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedRawAttachment
open GlobalSectionChangeIndex CommonReferenceNerve ModelSimplex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original raw polynomial reference, before actual source evaluation. -/
abbrev rawPolyRef := GlobalRawBass.InputIdentitySeedCarrier.polyRef g

/-- Actual base evaluation and its original total comparison attach every polynomial node. -/
def polynomialNode (N : Node (rawPolyRef g)) : Node (InputSeedCarrier.polyRef g) :=
  attachPrecompNode (rawPolyRef g) (evaluationModel (op Y)) (InputSeedCarrier.polyRef g)
    (evaluationComparisonIso (polynomial.map g ≫ projection.app Y)) N

/-- The original raw ordinary chart attachment. -/
def rawOrdinaryNode := attachPostcompNode (rawPolyRef g) (InputSeedCarrier.chart (X := X))
  (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
  (GlobalRawBass.InputIdentitySeedCarrier.ordinary g)

/-- The original mixed ordinary chart attachment. -/
def ordinaryNode := attachPostcompNode (InputSeedCarrier.polyRef g)
  (InputSeedCarrier.chart (X := X)) (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g)

/-- The actual first raw polynomial node pins the full ordinary attachment square. -/
theorem ordinary_source_node :
    InputSeedRawUnit.evaluateNode g
      (rawOrdinaryNode g (GlobalRawBass.InputIdentitySeedCarrier.polynomialNodes g 0)) =
    ordinaryNode g
      (polynomialNode g (GlobalRawBass.InputIdentitySeedCarrier.polynomialNodes g 0)) := by
  have hp := InputChartNormalizationNodes.commuting_normalization_nodes
    (polynomial.map g) (projection.app Y) (projection.app X) g (projection.naturality g) 0
  have hc := InputSpanTargetNodes.raw_nodes g plus GlobalRawBass.plus_projection 0
  have hr := InputRawDesc.chart_node g plus GlobalRawBass.plus_projection
    (BoundedFlatPerfectProjectionChartSquareRow.polynomialRow 0)
  have ha := BoundedFlatPerfectProjectionChartSquareRow.polynomial_row_nodes
    (projection.app Y) (plus.app Y) (projection.app X) (plus.app X) g
    (polynomial.map g) (laurent.map g) (projection.naturality g) (plus.naturality g)
    (GlobalRawBass.laurentProjection.app Y) (GlobalRawBass.plus_projection Y) 0
  exact (hc.trans (hr.trans (congrArg (InputSeedRawUnit.evaluateNode g) ha))).symm.trans
    (congrArg (ordinaryNode g) hp)

/-- The entire full-node ordinary square follows from its actual shared source anchor. -/
theorem ordinary_node (N : Node (rawPolyRef g)) :
    InputSeedRawUnit.evaluateNode g (rawOrdinaryNode g N) =
      ordinaryNode g (polynomialNode g N) := by
  exact prePost_families_match (InputSeedCarrier.laurentRef g) (evaluationModel (op Y))
    (InputSeedCarrier.chart (X := X)) (rawPolyRef g) (fun M => M)
    (fun M => pre_post_node (InputSeedCarrier.laurentRef g) (evaluationModel (op Y))
      (InputSeedCarrier.chart (X := X)) (rawPolyRef g) (fun M => M)
      (GlobalRawBass.InputIdentitySeedCarrier.ordinary g)
      (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)) M)
    (fun M => post_pre_node (InputSeedCarrier.laurentRef g) (evaluationModel (op Y))
      (InputSeedCarrier.chart (X := X)) (rawPolyRef g) (fun M => M)
      (evaluationComparisonIso (polynomial.map g ≫ projection.app Y))
      (InputSeedCarrier.ordinary g) M)
    (GlobalRawBass.InputIdentitySeedCarrier.polynomialNodes g 0) (ordinary_source_node g) N

/-- The separate actual shifted raw attachment. -/
def rawShiftedNode := attachPostcompNode (rawPolyRef g) (InputSeedCarrier.chart (X := X))
  (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
  (GlobalRawBass.InputIdentitySeedCarrier.shifted g)

/-- The separate actual shifted mixed attachment. -/
def shiftedNode := attachPostcompNode (InputSeedCarrier.polyRef g)
  (InputSeedCarrier.chart (X := X)) (InputSeedCarrier.laurentRef g) (InputSeedCarrier.shifted g)

/-- The original source-unit equation gives the entire second full-node attachment square. -/
theorem shifted_node (N : Node (rawPolyRef g)) :
    InputSeedRawUnit.evaluateNode g (rawShiftedNode g N) =
      shiftedNode g (polynomialNode g N) := by
  have hraw := reanchor_attach_node (rawPolyRef g) (InputSeedCarrier.chart (X := X))
    (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g) (InputSeedRawUnit.rawUnit g)
    (GlobalRawBass.InputIdentitySeedCarrier.ordinary g) N
  have hmixed := InputSeedCarrier.shifted_node g (polynomialNode g N)
  exact (congrArg (InputSeedRawUnit.evaluateNode g) hraw.symm).trans
    ((InputSeedRawUnit.evaluate_shift g (rawOrdinaryNode g N)).symm.trans
      ((congrArg (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))
        (ordinary_node g N)).trans hmixed))

/-- The actual polynomial map retains all original full reference nodes. -/
def polynomialParameter := mapParameter (polynomialNode g)

/-- The actual Laurent map retains the full original total evaluation comparison. -/
def laurentParameter := mapParameter (InputSeedRawUnit.evaluateNode g)

private theorem parameter_square {V W V' W' T : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (G : V ⟶ T) (F' : V' ⟶ W') (G' : V' ⟶ T)
    (a : Node F → Node G) (b : Node F' → Node G')
    (p : Node F → Node F') (q : Node G → Node G')
    (h : ∀ N, q (a N) = b (p N)) (y : |nerve (Codiscrete (Node F))|) :
    mapParameter q (mapParameter a y) = mapParameter b (mapParameter p y) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F y
  rw [← hz, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns => parameter G' ns z) (funext fun i => h (N i))

/-- The complete ordinary attaching square agrees on every original nerve parameter. -/
theorem ordinary_parameter (y : |nerve (Codiscrete (Node (rawPolyRef g)))|) :
    laurentParameter g (mapParameter (rawOrdinaryNode g) y) =
      mapParameter (ordinaryNode g) (polynomialParameter g y) :=
  parameter_square (rawPolyRef g) (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
    (InputSeedCarrier.polyRef g) (InputSeedCarrier.laurentRef g)
    (rawOrdinaryNode g) (ordinaryNode g) (polynomialNode g)
    (InputSeedRawUnit.evaluateNode g) (ordinary_node g) y

/-- The second entire attaching square preserves the distinct original Laurent-unit sheet. -/
theorem shifted_parameter (y : |nerve (Codiscrete (Node (rawPolyRef g)))|) :
    laurentParameter g (mapParameter (rawShiftedNode g) y) =
      mapParameter (shiftedNode g) (polynomialParameter g y) :=
  parameter_square (rawPolyRef g) (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
    (InputSeedCarrier.polyRef g) (InputSeedCarrier.laurentRef g)
    (rawShiftedNode g) (shiftedNode g) (polynomialNode g)
    (InputSeedRawUnit.evaluateNode g) (shifted_node g) y

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedRawAttachment
