/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityPositiveFactor
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputDescNative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0MergedBoundary
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1FirstPolynomialRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1SecondPolynomialRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumProjectionRectangleParameters
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitPrismNodes
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenCompactFamily
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceReanchorAttachment

/-!
# The actual two-tip carrier for the original global input seed

The polynomial square and original Laurent total are the native reference maps. Their
ordinary attachment is the full polynomial-column anchor of the original positive rectangle.
The other attachment uses the original forward unit on that same Laurent reference. The
whole original polynomial movement attaches before native evaluation, including its four
ordered primitive edges and nonmonotone five-node word.

The scheme-arrow attachment follows the original carrier at Quillen revision c561118b.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen SmallWaldhausenCategory AlgebraicGeometry.RingedSpace SSet
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedCarrier
open CommonReferenceNerve ModelSimplex
open BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectNativeMergedRows
open BoundedFlatCoefficientBassH1Join (nativeMiddleReference native_middle_column
  native_last_column post_square_second_nodes)
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

/-- The five vertices of the polynomial column in the positive rectangle. -/
def polynomialRow : Fin 5 → Fin 18 := ![5, 6, 13, 7, 17]

section Row

open BoundedFlatPerfectNativeSquareFiveSimplex

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

/-- Identify the native polynomial reference with the composite chart source. -/
def polynomialAnchor : (BoundedFlatPerfectProjectionReference.reference c r).hom.toFunctor ≅
    (source b p ≫ normalizedMap q').hom.toFunctor :=
  nativeMiddleReference p q q' b c hq r hr ≪≫ BoundedFlatPerfectBinarySimplex.total q' (b ≫ p)

private theorem polynomial_first_nodes (i : Fin 3) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
      (polynomialRow (firstFace.toOrderHom i)) =
      postReferenceNode (BoundedFlatPerfectProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (binaryNodes b p i) := by
  have hi : polynomialRow (firstFace.toOrderHom i) =
      BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  exact native_middle_column p q p' q' a b c hp hq r hr i

private theorem polynomial_second_nodes (i : Fin 3) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
      (polynomialRow (secondFace.toOrderHom i)) =
      postReferenceNode (BoundedFlatPerfectProjectionReference.reference c r) (normalizedMap q')
        (H := source p' a)
        (nativeLastReference p q p' q' a b c hp hq r hr ≪≫
          BoundedFlatPerfectBinarySimplex.total q' (p' ≫ a)) (binaryNodes p' a i) := by
  have hi : polynomialRow (secondFace.toOrderHom i) =
      BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i) := by
    fin_cases i <;> rfl
  rw [hi]
  exact native_last_column p q p' q' a b c hp hq r hr i

private theorem polynomial_row_nodes (i : Fin 5) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr (polynomialRow i) =
      postReferenceNode (BoundedFlatPerfectProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (nodes b p p' a hp i) := by
  have hs (k : Fin 3) :
      BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
        (polynomialRow (secondFace.toOrderHom k)) =
      postReferenceNode (BoundedFlatPerfectProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (nodes b p p' a hp (secondFace.toOrderHom k)) :=
    post_families_match (BoundedFlatPerfectProjectionReference.reference c r) (normalizedMap q')
      (source p' a) (binaryNodes p' a)
      (polynomial_second_nodes p q p' q' a b c hp hq r hr)
      (post_square_second_nodes b p p' a hp (BoundedFlatPerfectProjectionReference.reference c r)
        (normalizedMap q') (polynomialAnchor p q q' b c hq r hr)) 0
      (polynomial_first_nodes p q p' q' a b c hp hq r hr 0) k
  fin_cases i
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 0
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 1
  · exact polynomial_first_nodes p q p' q' a b c hp hq r hr 2
  · exact hs 1
  · exact hs 2

end Row

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual polynomial square source, before either normalization track. -/
abbrev polyRef := BoundedFlatPerfectNativeSquareFiveSimplex.source (polynomial.map g)
  (projection.app Y)

/-- The original normalized positive chart model map. -/
abbrev chart := normalizedMap (plus.app X)

/-- The actual outer Laurent total used by both original input rectangles. -/
abbrev laurentRef := InputDescSimplex.reference g

/-- The original five polynomial nodes include their complete equality-induced references. -/
abbrev polynomialNodes := BoundedFlatPerfectNativeSquareFiveSimplex.nodes (polynomial.map g)
  (projection.app Y) (projection.app X) g (projection.naturality g)

/-- The full polynomial-column reference, retaining the actual chart-square and projection. -/
def ordinary : (laurentRef g).hom.toFunctor ≅ (polyRef g ≫ chart (X := X)).hom.toFunctor :=
  polynomialAnchor (projection.app Y) (plus.app Y)
    (plus.app X) (polynomial.map g) (laurent.map g) (plus.naturality g)
    (laurentProjection.app Y) (plus_projection Y)

/-- The original forward unit on the actual old Laurent total. -/
def commonUnit : (laurentRef g).hom.toFunctor ≅ (laurentRef g).hom.toFunctor :=
  UnitTrackPostcompSimplex.sourceUnit (laurent.map g) (laurentProjection.app Y)
    (laurentScalar (op Y))

/-- The separate shifted attachment keeps the full original unit before the ordinary anchor. -/
def shifted : (laurentRef g).hom.toFunctor ≅ (polyRef g ≫ chart (X := X)).hom.toFunctor :=
  commonUnit g ≪≫ ordinary g

/-- The actual two-tip carrier; its polynomial tips are kept distinct. -/
abbrev Carrier := CutOpenCarrier.space (polyRef g) (chart (X := X)) (laurentRef g)
  (ordinary g) (shifted g)

/-- The entire original polynomial square moves in its own full-node nerve. -/
def movement : C(I, |nerve (Codiscrete (Node (polyRef g)))|) :=
  (parameter (polyRef g) (polynomialNodes g)).comp
    BoundedFlatPerfectNativeSquareFiveSimplex.parameter.toContinuousMap

/-- Every original polynomial-square value is recovered at its own unchanged time. -/
theorem movement_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    pointwisePrespectrumFamily (polyRef g) n (movement g t) x =
      (polynomialSquareHomotopy g).level n (t, x) := by
  change pointwisePrespectrumFamily (polyRef g) n
    (parameter (polyRef g) (polynomialNodes g)
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t)) x = _
  rw [pointwisePrespectrumFamily_parameter]
  exact BoundedFlatPerfectNativeSquareFiveSimplex.native (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g) n t x

/-- All five original polynomial-column nodes attach with their full reference isomorphisms. -/
theorem polynomial_nodes (i : Fin 5) :
    InputDescSimplex.nodes g (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (polynomialRow i)) =
    attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g)
      (polynomialNodes g i) := by
  rw [InputDescSimplex.plus_nodes]
  exact polynomial_row_nodes
    (projection.app Y) (plus.app Y) (projection.app X) (plus.app X) g
    (polynomial.map g) (laurent.map g) (projection.naturality g) (plus.naturality g)
    (laurentProjection.app Y) (plus_projection Y) i

/-- The two monotone triangles in the nonmonotone five-node polynomial word. -/
def polynomialFirstFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 13], by decide⟩

/-- The second polynomial face with ordered vertices 5, 7 and 28. -/
def polynomialSecondFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 7, 28], by decide⟩

private theorem polynomial_first_parameter (t : I) :
    parameter (laurentRef g) (InputDescSimplex.nodes g)
        (binaryPath (k := 30) 5 6 13 t) =
      parameter (laurentRef g)
        (fun i ↦ attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g)
          (ordinary g) (polynomialNodes g i))
        (binaryPath (k := 4) 0 1 2 t) := by
  let z := binaryPath (k := 2) 0 1 2 t
  have h₁ := parameter_face (laurentRef g) (InputDescSimplex.nodes g) polynomialFirstFace z
  have h₂ := parameter_face (laurentRef g)
    (fun i ↦ attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (polynomialNodes g i))
    BoundedFlatPerfectNativeSquareFiveSimplex.firstFace z
  have hindex (i : Fin 3) : polynomialFirstFace.toOrderHom i =
      BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
        (polynomialRow (BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i)) := by
    fin_cases i <;> rfl
  have hnodes (i : Fin 3) :
      InputDescSimplex.nodes g (polynomialFirstFace.toOrderHom i) =
        attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g)
          (polynomialNodes g
            (BoundedFlatPerfectNativeSquareFiveSimplex.firstFace.toOrderHom i)) := by
    rw [hindex]
    exact polynomial_nodes g _
  have he := h₁.trans ((congrArg (fun ns ↦ parameter (laurentRef g) ns z)
    (funext hnodes)).trans h₂.symm)
  dsimp only [z] at he
  rw [BoundedFlatCoefficientBassH0Merged.map_any_binary,
    BoundedFlatCoefficientBassH0Merged.map_any_binary] at he
  exact he

private theorem polynomial_second_parameter (t : I) :
    parameter (laurentRef g) (InputDescSimplex.nodes g)
        (binaryPath (k := 30) 5 7 28 t) =
      parameter (laurentRef g)
        (fun i ↦ attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g)
          (ordinary g) (polynomialNodes g i))
        (binaryPath (k := 4) 0 3 4 t) := by
  let z := binaryPath (k := 2) 0 1 2 t
  have h₁ := parameter_face (laurentRef g) (InputDescSimplex.nodes g) polynomialSecondFace z
  have h₂ := parameter_face (laurentRef g)
    (fun i ↦ attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (polynomialNodes g i))
    BoundedFlatPerfectNativeSquareFiveSimplex.secondFace z
  have hindex (i : Fin 3) : polynomialSecondFace.toOrderHom i =
      BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
        (polynomialRow (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i)) := by
    fin_cases i <;> rfl
  have hnodes (i : Fin 3) :
      InputDescSimplex.nodes g (polynomialSecondFace.toOrderHom i) =
        attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g)
          (polynomialNodes g
            (BoundedFlatPerfectNativeSquareFiveSimplex.secondFace.toOrderHom i)) := by
    rw [hindex]
    exact polynomial_nodes g _
  have he := h₁.trans ((congrArg (fun ns ↦ parameter (laurentRef g) ns z)
    (funext hnodes)).trans h₂.symm)
  dsimp only [z] at he
  rw [BoundedFlatCoefficientBassH0Merged.map_any_binary,
    BoundedFlatCoefficientBassH0Merged.map_any_binary] at he
  exact he

/-- The whole ordinary rail follows the same two native triangles and original times. -/
theorem movement_attach (t : I) :
    parameter (laurentRef g) (InputDescSimplex.nodes g)
      (BoundedFlatPerfectProjectionRectangleParameters.Ppath
        BoundedFlatCoefficientBassH0Diagram.plusFace t) =
    mapParameter (attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g))
      (movement g t) := by
  change _ = mapParameter _ (parameter (polyRef g) (polynomialNodes g)
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter t))
  rw [mapParameter_parameter]
  change
    parameter (laurentRef g) (InputDescSimplex.nodes g)
      (((binaryPath (k := 30) 5 6 13).symm.trans (binaryPath 5 7 28)) t) =
    parameter (laurentRef g)
      (fun i ↦ attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (polynomialNodes g i))
      (((binaryPath (k := 4) 0 1 2).symm.trans (binaryPath 0 3 4)) t)
  rw [Path.trans_apply, Path.trans_apply]
  split
  · exact polynomial_first_parameter g _
  · exact polynomial_second_parameter g _

/-- A complete shifted attached node retains the original common unit and ordinary anchor. -/
theorem shifted_node (N : Node (polyRef g)) :
    reanchorNode (commonUnit g)
      (attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g) N) =
    attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (shifted g) N := by
  apply congrArg (fun a ↦ (⟨N.1 ≫ chart (X := X), a⟩ : Node (laurentRef g)))
  exact (Iso.trans_assoc _ _ _).symm

/-- The whole shifted polynomial rail uses the same movement with its separate attachment. -/
theorem shifted_movement_attach (t : I) :
    mapParameter (reanchorNode (commonUnit g))
      (parameter (laurentRef g) (InputDescSimplex.nodes g)
        (BoundedFlatPerfectProjectionRectangleParameters.Ppath
          BoundedFlatCoefficientBassH0Diagram.plusFace t)) =
    mapParameter (attachPostcompNode (polyRef g) (chart (X := X)) (laurentRef g) (shifted g))
      (movement g t) := by
  rw [movement_attach]
  exact reanchor_attach_parameter (polyRef g) (chart (X := X)) (laurentRef g)
    (commonUnit g) (ordinary g) (movement g t)

/-- The two actual tips remain different even though both evaluate to the native cone point. -/
theorem tips_distinct :
    CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g) (shifted g) ≠
    CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g) (ordinary g) (shifted g) :=
  CutOpenCarrier.tips_ne _ _ _ _ _

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedCarrier
