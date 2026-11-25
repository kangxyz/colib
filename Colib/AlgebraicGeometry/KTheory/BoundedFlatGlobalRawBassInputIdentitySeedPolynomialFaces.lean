/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedLaurentFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0MergedBoundary

/-!
# The actual polynomial identity faces in the two-tip seed carrier

All eight nodes of the original projection unit square are moved to the unchanged raw
polynomial reference. The original five-node polynomial movement, all eight attachment
nodes, and the two split identity rails are retained with their full references. The two
cone sheets use the same polynomial family without identifying their tips.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedPolynomialFaces
open CommonReferenceNerve ModelSimplex InputIdentitySeedCarrier
open BoundedFlatPerfectProjectionBinaryRows (binaryNodes)
open BoundedFlatPerfectOriginalUnitSquareSimplex

private theorem reanchor_refl {V W : WideSubcategory preservesZero.{u}} {F : V ⟶ W}
    (N : Node F) : reanchorNode (Iso.refl F.hom.toFunctor) N = N := by
  rcases N with ⟨G, η⟩
  simp [reanchorNode]

private theorem anchor_post_node {V W T : WideSubcategory preservesZero.{u}}
    {F G : V ⟶ T} {H : V ⟶ W} (J : W ⟶ T)
    (η : F.hom.toFunctor ≅ G.hom.toFunctor)
    (ρ : G.hom.toFunctor ≅ (H ≫ J).hom.toFunctor) (N : Node H) :
    reanchorNode η (postReferenceNode G J ρ N) =
      postReferenceNode F J (η ≪≫ ρ) N := by
  rcases N with ⟨K, κ⟩
  exact reanchorNode_assoc η ρ ⟨K ≫ J, isoWhiskerRight κ J.hom.toFunctor⟩

private theorem post_anchor_node {V W T : WideSubcategory preservesZero.{u}}
    (F : V ⟶ T) (J : W ⟶ T) {H G : V ⟶ W}
    (ρ : F.hom.toFunctor ≅ (H ≫ J).hom.toFunctor) (η : H.hom.toFunctor ≅ G.hom.toFunctor)
    (N : Node G) :
    postReferenceNode F J ρ (reanchorNode η N) =
      postReferenceNode F J (ρ ≪≫ isoWhiskerRight η J.hom.toFunctor) N := by
  rcases N with ⟨K, κ⟩
  apply congrArg (fun ν : F.hom.toFunctor ≅ (K ≫ J).hom.toFunctor ↦
    (⟨K ≫ J, ν⟩ : Node F))
  change ρ ≪≫ isoWhiskerRight (η ≪≫ κ) J.hom.toFunctor = _
  rw [isoWhiskerRight_trans, Iso.trans_assoc]

/-- The actual eight-node unit-square family before the polynomial reference transport. -/
def unitNodes {A B : Scheme.{u}} (f : A ⟶ B) (i : Fin 8) : Node (sourceMap f) :=
  ⟨vertices f i, references f i⟩

/-- Functorial identity transport is reduced at a generic arrow before any scheme specialization. -/
theorem source_transport {A B : Scheme.{u}} (f : A ⟶ B)
    (a : A ⟶ A) (ha : a = 𝟙 A) :
    (BoundedFlatPerfectNativeSquareFiveSimplex.source a f).hom.toFunctor =
      (sourceMap f).hom.toFunctor := by
  subst a
  exact (BoundedFlatPerfectOriginalUnitSquareSimplex.rightBinarySourceEq f).symm

private theorem five_transport {A B : Scheme.{u}} (f : A ⟶ B)
    (a : A ⟶ A) (ha : a = 𝟙 A) (h : a ≫ f = f ≫ 𝟙 B)
    (e : (BoundedFlatPerfectNativeSquareFiveSimplex.source a f).hom.toFunctor =
      (sourceMap f).hom.toFunctor)
    (i : Fin 5) :
    reanchorNode (eqToIso e) (unitNodes f (![0, 1, 2, 4, 5] i)) =
      BoundedFlatPerfectNativeSquareFiveSimplex.nodes a f f (𝟙 B) h i := by
  subst a
  have hr (j : Fin 3) :
      reanchorNode (eqToIso e) (unitNodes f (![0, 1, 2] j)) =
        binaryNodes (𝟙 A) f j := by
    change reanchorNode (eqToIso e)
      (⟨vertices f (![0, 1, 2] j), references f (![0, 1, 2] j)⟩ : Node (sourceMap f)) = _
    rw [BoundedFlatPerfectOriginalUnitSquareSimplex.unit_right_row, reanchorNode_assoc,
      eqToIso_trans]
    rcases binaryNodes (𝟙 A) f j with ⟨G, η⟩
    simp [reanchorNode]
  have hl (j : Fin 3) :
      reanchorNode (eqToIso e) (unitNodes f (![0, 4, 5] j)) =
        reanchorNode (BoundedFlatPerfectNativeSquareFiveSimplex.sourceIso (𝟙 A) f f (𝟙 B) h)
          (binaryNodes f (𝟙 B) j) := by
    change reanchorNode (eqToIso e)
      (⟨vertices f (![0, 4, 5] j), references f (![0, 4, 5] j)⟩ : Node (sourceMap f)) = _
    rw [BoundedFlatPerfectOriginalUnitSquareSimplex.unit_left_row, reanchorNode_assoc,
      eqToIso_trans]
    rfl
  fin_cases i
  · exact hr 0
  · exact hr 1
  · exact hr 2
  · exact hl 1
  · exact hl 2

variable (X : Scheme.{u})

/-- The actual functorial identity transport points from the raw reference to the unit square. -/
def b : (polyRef (𝟙 X)).hom.toFunctor ≅ (sourceMap (projection.app X)).hom.toFunctor :=
  eqToIso (source_transport (projection.app X) (polynomial.map (𝟙 X)) (polynomial.map_id X))

/-- Eight actual projection unit-square nodes, with their complete raw polynomial references. -/
def K (i : Fin 8) : Node (polyRef (𝟙 X)) :=
  reanchorNode (b X) (unitNodes (projection.app X) i)

/-- The old five polynomial nodes retain their precise map-id and square-equality transport. -/
theorem rawFive_nodes (i : Fin 5) :
    K X (![0, 1, 2, 4, 5] i) = polynomialNodes (𝟙 X) i :=
  five_transport (projection.app X) (polynomial.map (𝟙 X)) (polynomial.map_id X)
    (projection.naturality (𝟙 X)) _ i

/-- The complete normalized terminal node is exactly the original source node. -/
theorem terminal_node : K X 7 = K X 0 := by
  apply congrArg (reanchorNode (b X))
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  exact InputIdentityCarrierProjection.right_route_identity (projection.app X)

/-- One full shared polynomial node fixes the attachment of the entire eight-node family. -/
theorem attachment_forward (i : Fin 8) :
    reanchorNode (InputIdentityNodes.inputSourceIso X)
      (attachPostcompNode (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
        (ordinary (𝟙 X)) (K X i)) = InputIdentityTopNodes.plusNodes X i := by
  apply post_families_match (InputIdentityNodes.source X) (chart (X := X))
    (sourceMap (projection.app X)) (unitNodes (projection.app X))
    (fun j ↦ (anchor_post_node (chart (X := X)) (InputIdentityNodes.inputSourceIso X)
      (ordinary (𝟙 X)) (K X j)).trans
        (post_anchor_node (InputIdentityNodes.source X) (chart (X := X))
          (InputIdentityNodes.inputSourceIso X ≪≫ ordinary (𝟙 X)) (b X)
          (unitNodes (projection.app X) j))) (fun _ ↦ rfl) 0 ?_ i
  have h := InputIdentityBoundaryNodes.h0_plus_top X 0
  change reanchorNode (InputIdentityNodes.inputSourceIso X)
    (InputDescSimplex.nodes (𝟙 X) (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (InputIdentitySeedCarrier.polynomialRow 0))) =
        InputIdentityTopNodes.plusNodes X 0 at h
  rw [InputIdentitySeedCarrier.polynomial_nodes] at h
  have hz := rawFive_nodes X 0
  change K X 0 = polynomialNodes (𝟙 X) 0 at hz
  exact (congrArg (fun N ↦ reanchorNode (InputIdentityNodes.inputSourceIso X)
    (attachPostcompNode (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) N)) hz).trans h

/-- Every attachment node is the original identity node transported back to the raw reference. -/
theorem attachment_nodes (i : Fin 8) :
    attachPostcompNode (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (K X i) =
    reanchorNode (InputIdentityNodes.inputSourceIso X).symm
      (InputIdentityTopNodes.plusNodes X i) := by
  have h := congrArg (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
    (attachment_forward X i)
  rwa [reanchorNode_assoc, Iso.symm_self_id, reanchor_refl] at h

/-- The whole eight-node attachment agrees before any native evaluation or boundary restriction. -/
theorem attachment_parameter (z : StdSimplex ℝ (Fin 8)) :
    mapParameter (attachPostcompNode (polyRef (𝟙 X)) (chart (X := X))
      (laurentRef (𝟙 X)) (ordinary (𝟙 X))) (parameter (polyRef (𝟙 X)) (K X) z) =
    InputIdentitySeedLaurentFaces.back X
      (parameter (InputIdentityNodes.source X) (InputIdentityTopNodes.plusNodes X) z) := by
  change mapParameter _ (parameter _ _ z) = mapParameter _ (parameter _ _ z)
  rw [mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun N : Fin 8 → Node (laurentRef (𝟙 X)) ↦
    parameter (laurentRef (𝟙 X)) N z) (funext (attachment_nodes X))

/-- Reanchoring preserves the original entire polynomial simplex, including native level zero. -/
theorem nodes_native (n : ℕ) (z : StdSimplex ℝ (Fin 8))
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    pointwisePrespectrumFamily (polyRef (𝟙 X)) n
      (parameter (polyRef (𝟙 X)) (K X) z) x =
    prespectrumSimplexFamily (simplex (projection.app X)) n (z, x) := by
  rw [pointwisePrespectrumFamily_parameter]
  change prespectrumSimplexFamily (reanchorSimplex (b X) (unitNodes (projection.app X)))
      n (z, x) = _
  rw [reanchorSimplex_eq]; rfl

/-- The whole actual polynomial identity square uses its original rotation and quotient clocks. -/
def square : C(I × I, |nerve (Codiscrete (Node (polyRef (𝟙 X))))|) :=
  (parameter (polyRef (𝟙 X)) (K X)).comp squareParameter

/-- Every square point is the fixed polynomialSquare, with no replacement homotopy. -/
theorem square_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    pointwisePrespectrumFamily (polyRef (𝟙 X)) n (square X (r, s)) x =
      (InputIdentity.polynomialSquare X).level n (r, (s, x)) :=
  (nodes_native X n (squareParameter (r, s)) x).trans
    (BoundedFlatPerfectOriginalUnitSquareSimplex.square_native (projection.app X) n r s x)

/-- The target identity rail keeps the original two-piece word through nodes 2, 3, and 7. -/
def targetRail : C(I, |nerve (Codiscrete (Node (polyRef (𝟙 X))))|) :=
  (parameter (polyRef (𝟙 X)) (K X)).comp
    (binaryPath (k := 7) 2 3 7).toContinuousMap

/-- The source identity rail keeps the different original word through nodes 5, 6, and 7. -/
def sourceRail : C(I, |nerve (Codiscrete (Node (polyRef (𝟙 X))))|) :=
  (parameter (polyRef (𝟙 X)) (K X)).comp
    (binaryPath (k := 7) 5 6 7).toContinuousMap

/-- The entire left boundary is the unchanged target identity rail. -/
theorem square_left (r : I) : square X (r, 0) = targetRail X r := by
  change parameter (polyRef (𝟙 X)) (K X) (squareParameter (r, 0)) =
    parameter (polyRef (𝟙 X)) (K X) (rightUnitPath r)
  apply congrArg (parameter (polyRef (𝟙 X)) (K X))
  rw [BoundedFlatPerfectOriginalUnitSquareSimplex.square_left]
  have h : ThreeSideSquare.leftTime r = FundamentalGroupoid.OpenCover.leftHalf
      (FundamentalGroupoid.OpenCover.leftHalf r) := by
    apply Subtype.ext
    simp only [FundamentalGroupoid.OpenCover.coe_leftHalf]
    dsimp [ThreeSideSquare.leftTime]
    ring
  rw [h, FundamentalGroupoid.OpenCover.trans_leftHalf,
    FundamentalGroupoid.OpenCover.trans_leftHalf]

/-- The entire right boundary is the unchanged source identity rail. -/
theorem square_right (r : I) : square X (r, 1) = sourceRail X r := by
  change parameter (polyRef (𝟙 X)) (K X) (squareParameter (r, 1)) =
    parameter (polyRef (𝟙 X)) (K X) (leftUnitPath r)
  apply congrArg (parameter (polyRef (𝟙 X)) (K X))
  rw [BoundedFlatPerfectOriginalUnitSquareSimplex.square_right]
  rw [← Path.extend_apply _ (ThreeSideSquare.rightTime r).property]
  rw [Path.extend_trans_of_half_le _ _ (by
    dsimp [ThreeSideSquare.rightTime]
    linarith [r.2.2]), Path.extend_symm_apply]
  have he : 1 - (2 * (ThreeSideSquare.rightTime r : ℝ) - 1) = (r : ℝ) := by
    dsimp [ThreeSideSquare.rightTime]
    ring
  rw [he, Path.extend_apply _ r.property]

/-- The actual ordered five-node face includes both original polynomial intermediates. -/
def rawFiveFace : ⦋4⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 4, 5], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The complete initial square boundary is the original five-node polynomial movement. -/
theorem square_initial (s : I) : square X (0, s) = movement (𝟙 X) s := by
  change parameter (polyRef (𝟙 X)) (K X) (squareParameter (0, s)) =
    parameter (polyRef (𝟙 X)) (polynomialNodes (𝟙 X))
      (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s)
  rw [BoundedFlatPerfectOriginalUnitSquareSimplex.square_zero]
  have hs := BoundedFlatCoefficientBassH0Merged.map_two_binary rawFiveFace.toOrderHom 0 1 2 3 4 s
  change StdSimplex.map rawFiveFace.toOrderHom
    (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s) =
    (rightCompositionPath.symm.trans leftCompositionPath) s at hs
  rw [← hs, parameter_face]
  exact congrArg (fun N : Fin 5 → Node (polyRef (𝟙 X)) ↦
    parameter (polyRef (𝟙 X)) N (BoundedFlatPerfectNativeSquareFiveSimplex.parameter s))
      (funext (rawFive_nodes X))

private theorem parameter_vertex {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) {k : ℕ}
    (N : Fin (k + 1) → Node F) (i : Fin (k + 1)) :
    parameter F N (StdSimplex.single i) =
      parameter F (fun _ : Fin 1 ↦ N i) (StdSimplex.single 0) := by
  let α : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_refl i⟩
  have hm : StdSimplex.map α.toOrderHom
      (StdSimplex.single (0 : Fin 1) : StdSimplex ℝ (Fin 1)) = StdSimplex.single i := by
    rw [StdSimplex.map_single]
    rfl
  rw [← hm, parameter_face]
  rfl

/-- The unchanged polynomial source vertex is also the terminal vertex of both identity rails. -/
def basePoint : |nerve (Codiscrete (Node (polyRef (𝟙 X))))| :=
  parameter (polyRef (𝟙 X)) (K X) (StdSimplex.single 0)

/-- The whole terminal square boundary is the actual original source point, not just its image. -/
theorem square_terminal (s : I) : square X (1, s) = basePoint X := by
  change parameter (polyRef (𝟙 X)) (K X) (squareParameter (1, s)) =
    parameter (polyRef (𝟙 X)) (K X) (StdSimplex.single 0)
  have h : squareParameter (1, s) = (StdSimplex.single 7 : StdSimplex ℝ (Fin 8)) := by
    rw [BoundedFlatPerfectOriginalUnitSquareSimplex.square_top]
    rw [← Path.extend_apply _ (ThreeSideSquare.topTime s).property]
    rw [Path.extend_trans_of_le_half _ _ (by
      dsimp [ThreeSideSquare.topTime]
      linarith [s.2.2])]
    rw [Path.extend_trans_of_half_le _ _ (by
      dsimp [ThreeSideSquare.topTime]
      linarith [s.2.1])]
    have he : 2 * (2 * (ThreeSideSquare.topTime s : ℝ)) - 1 = (s : ℝ) := by
      dsimp [ThreeSideSquare.topTime]
      ring
    rw [he, Path.extend_apply _ s.property]; rfl
  rw [h, parameter_vertex (polyRef (𝟙 X)) (K X) 7]
  exact (congrArg (fun N : Node (polyRef (𝟙 X)) ↦
    parameter (polyRef (𝟙 X)) (fun _ : Fin 1 ↦ N) (StdSimplex.single 0))
      (terminal_node X)).trans (parameter_vertex (polyRef (𝟙 X)) (K X) 0).symm

/-- The target identity rail starts at the original old polynomial cone input. -/
theorem targetRail_zero : targetRail X 0 = movement (𝟙 X) 0 :=
  (square_left X 0).symm.trans (square_initial X 0)

/-- The source identity rail starts at the original new polynomial cone input. -/
theorem sourceRail_zero : sourceRail X 0 = movement (𝟙 X) 1 :=
  (square_right X 0).symm.trans (square_initial X 1)

/-- The whole target rail ends at the unchanged source point. -/
theorem targetRail_one : targetRail X 1 = basePoint X :=
  (square_left X 1).symm.trans (square_terminal X 0)

/-- The whole source rail has the very same full-reference endpoint. -/
theorem sourceRail_one : sourceRail X 1 = basePoint X :=
  (square_right X 1).symm.trans (square_terminal X 1)

/-- The original polynomial map identity acts after the unchanged projection at every time. -/
theorem targetRail_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    pointwisePrespectrumFamily (polyRef (𝟙 X)) n (targetRail X r) x =
      (InputIdentity.polynomialHomotopy X).level n
        (r, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x) := by
  rw [← square_left]
  exact (square_native X n r 0 x).trans ((InputIdentity.polynomialSquare X).left n r x)

/-- The unchanged source identity acts before the original projection at every time. -/
theorem sourceRail_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    pointwisePrespectrumFamily (polyRef (𝟙 X)) n (sourceRail X r) x =
      (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n
        ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x)) := by
  rw [← square_right]
  exact (square_native X n r 1 x).trans ((InputIdentity.polynomialSquare X).right n r x)

/-- Every polynomial parameter attaches to the same complete old identity face on either sheet. -/
theorem cylinder_zero (e : Bool) (z : StdSimplex ℝ (Fin 8)) :
    InputIdentitySeedCone.cylinder (𝟙 X) e
      (parameter (polyRef (𝟙 X)) (K X) z, 0) =
    InputIdentitySeedLaurentFaces.sheet X e
      (parameter (InputIdentityNodes.source X) (InputIdentityTopNodes.plusNodes X) z) := by
  cases e
  · change CutOpenCarrier.cylinderMinus _ _ _ _ _ (_, 0) = _
    rw [CutOpenCarrier.cylinderMinus_zero, attachment_parameter]; rfl
  · change CutOpenCarrier.cylinderPlus _ _ _ _ _ (_, 0) = _
    rw [CutOpenCarrier.cylinderPlus_zero]
    change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (mapParameter (attachPostcompNode _ _ _ (commonUnit (𝟙 X) ≪≫ ordinary (𝟙 X)))
        (parameter (polyRef (𝟙 X)) (K X) z)) = _
    rw [← reanchor_attach_parameter, attachment_parameter]; rfl

/-- At every cone height, the target rail begins on the original old cone of its own sheet. -/
theorem targetCone_initial (e : Bool) (s : I) :
    InputIdentitySeedCone.cylinder (𝟙 X) e (targetRail X 0, s) =
      InputIdentitySeedCone.cylinder (𝟙 X) e (movement (𝟙 X) 0, s) :=
  congrArg (fun y ↦ InputIdentitySeedCone.cylinder (𝟙 X) e (y, s)) (targetRail_zero X)

/-- At every cone height, the source rail begins on the original new cone of its own sheet. -/
theorem sourceCone_initial (e : Bool) (s : I) :
    InputIdentitySeedCone.cylinder (𝟙 X) e (sourceRail X 0, s) =
      InputIdentitySeedCone.cylinder (𝟙 X) e (movement (𝟙 X) 1, s) :=
  congrArg (fun y ↦ InputIdentitySeedCone.cylinder (𝟙 X) e (y, s)) (sourceRail_zero X)

/-- Every terminal target-cone point keeps the original polynomial source and the selected tip. -/
theorem targetCone_terminal (e : Bool) (s : I) :
    InputIdentitySeedCone.cylinder (𝟙 X) e (targetRail X 1, s) =
      InputIdentitySeedCone.cylinder (𝟙 X) e (basePoint X, s) :=
  congrArg (fun y ↦ InputIdentitySeedCone.cylinder (𝟙 X) e (y, s)) (targetRail_one X)

/-- The source-cone terminal path is the same complete path on that particular sheet. -/
theorem sourceCone_terminal (e : Bool) (s : I) :
    InputIdentitySeedCone.cylinder (𝟙 X) e (sourceRail X 1, s) =
      InputIdentitySeedCone.cylinder (𝟙 X) e (basePoint X, s) :=
  congrArg (fun y ↦ InputIdentitySeedCone.cylinder (𝟙 X) e (y, s)) (sourceRail_one X)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedPolynomialFaces
