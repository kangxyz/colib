/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedUnitLift
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedCarrier
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceReanchorAttachment

/-!
# Full ordinary and shifted Laurent seams of the original global input seed

The five outer references of the original positive rectangle agree with the five lower
unit-pasting nodes. The actual source unit transports all five to their separate upper nodes.
Both entire movement words, both terminal unit rails, and the chosen unit comparison enter
the actual two-tip carrier without changing any of their coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters Topology Topology.LoopPrespectrum SSet
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u v
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedUnitSeams
open CommonReferenceNerve ModelSimplex InputIdentitySeedCarrier InputIdentitySeedUnitNodes

/-- The exact five common outer nodes in the original thirty-one-node diagram. -/
def rawOuterFace : ⦋4⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 25, 26], by decide⟩

/-- The lower five full reference nodes of the actual unit comparison. -/
def unitLowerFace : ⦋4⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 3, 4], by decide⟩

/-- The five distinct unit-shifted full reference nodes. -/
def unitShiftedFace : ⦋4⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 7, 8, 9], by decide⟩

/-- The unchanged inverse-first, forward-second binary movement word. -/
abbrev outerWord := (binaryPath (k := 4) 0 1 2).symm.trans (binaryPath 0 3 4)

private theorem prism_shift {V W : WideSubcategory preservesZero.{v}} (F G H : V ⟶ W)
    (e : F.hom.toFunctor ≅ G.hom.toFunctor) (n : G.hom.toFunctor ≅ H.hom.toFunctor)
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) (β : G.hom.toFunctor ≅ G.hom.toFunctor)
    (δ : H.hom.toFunctor ≅ H.hom.toFunctor)
    (he : e.hom ≫ β.hom = α.hom ≫ e.hom)
    (hn : β.hom ≫ n.hom = n.hom ≫ δ.hom) (i : Fin 3) :
    reanchorNode α (UnitPrismNodes.nodes F G H e n α β δ (Fin.castAdd 3 i)) =
      UnitPrismNodes.nodes F G H e n α β δ (Fin.natAdd 3 i) := by
  have he' : α ≪≫ e = e ≪≫ β := Iso.ext he.symm
  have hn' : β ≪≫ n = n ≪≫ δ := Iso.ext hn
  fin_cases i
  · change (⟨F, α ≪≫ Iso.refl _⟩ : CommonReferenceNerve.Node F) = ⟨F, α⟩
    rw [Iso.trans_refl]
  · change (⟨G, α ≪≫ e⟩ : CommonReferenceNerve.Node F) = ⟨G, e ≪≫ β⟩
    exact congrArg (fun ρ ↦ (⟨G, ρ⟩ : CommonReferenceNerve.Node F)) he'
  · change (⟨H, α ≪≫ (e ≪≫ n)⟩ : CommonReferenceNerve.Node F) =
      ⟨H, (e ≪≫ n) ≪≫ δ⟩
    apply congrArg (fun ρ ↦ (⟨H, ρ⟩ : CommonReferenceNerve.Node F))
    calc
      α ≪≫ (e ≪≫ n) = (α ≪≫ e) ≪≫ n := (Iso.trans_assoc _ _ _).symm
      _ = (e ≪≫ β) ≪≫ n := congrArg (fun ρ ↦ ρ ≪≫ n) he'
      _ = e ≪≫ (β ≪≫ n) := Iso.trans_assoc _ _ _
      _ = e ≪≫ (n ≪≫ δ) := congrArg (fun ρ ↦ e ≪≫ ρ) hn'
      _ = (e ≪≫ n) ≪≫ δ := (Iso.trans_assoc _ _ _).symm

private theorem anchor_square {V W : WideSubcategory preservesZero.{v}} {F G : V ⟶ W}
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) (ε : F.hom.toFunctor ≅ G.hom.toFunctor)
    (β : G.hom.toFunctor ≅ G.hom.toFunctor) (h : α ≪≫ ε = ε ≪≫ β)
    (N : CommonReferenceNerve.Node G) :
    reanchorNode α (reanchorNode ε N) = reanchorNode ε (reanchorNode β N) := by
  rcases N with ⟨H, ρ⟩
  change (⟨H, α ≪≫ (ε ≪≫ ρ)⟩ : CommonReferenceNerve.Node F) =
    ⟨H, ε ≪≫ (β ≪≫ ρ)⟩
  apply congrArg (fun ν ↦ (⟨H, ν⟩ : CommonReferenceNerve.Node F))
  exact (Iso.trans_assoc _ _ _).symm.trans
    ((congrArg (fun ν ↦ ν ≪≫ ρ) h).trans (Iso.trans_assoc _ _ _))

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every ordinary outer node agrees as a complete dependent reference. -/
theorem outer_nodes (i : Fin 5) :
    InputDescSimplex.nodes g (rawOuterFace.toOrderHom i) =
      nodes g (unitLowerFace.toOrderHom i) := by
  have hi : rawOuterFace.toOrderHom i =
      BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
        (BoundedFlatPerfectProjectionReference.sharedIndex i) := by
    fin_cases i <;> rfl
  rw [hi, InputDescSimplex.plus_nodes]
  change BoundedFlatPerfectProjectionReference.nodes (projection.app Y) (plus.app Y)
    (projection.app X) (plus.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (plus.naturality g) (laurentProjection.app Y)
    (plus_projection Y) (BoundedFlatPerfectProjectionReference.sharedIndex i) = _
  rw [BoundedFlatPerfectProjectionReference.shared_nodes (projection.app Y) (plus.app Y)
    (projection.app X) (plus.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (plus.naturality g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (plus_projection Y) (plus_projection X)]
  fin_cases i
  · rfl
  · rfl
  · change (⟨_, BoundedFlatPerfectBinarySimplex.total
      (laurent.map g) (laurentProjection.app Y)⟩ : InputIdentitySeedUnitNodes.Node g) =
      ⟨_, BoundedFlatPerfectBinarySimplex.first (laurent.map g) (laurentProjection.app Y) ≪≫
        BoundedFlatPerfectBinarySimplex.second (laurent.map g) (laurentProjection.app Y)⟩
    rw [show BoundedFlatPerfectBinarySimplex.first (laurent.map g) (laurentProjection.app Y) ≪≫
        BoundedFlatPerfectBinarySimplex.second (laurent.map g) (laurentProjection.app Y) =
        BoundedFlatPerfectBinarySimplex.total (laurent.map g) (laurentProjection.app Y) from
      Iso.ext (BoundedFlatPerfectBinarySimplex.small_composite_hom _ _)]
  · rfl
  · change (⟨_, sourceIso g ≪≫
      BoundedFlatPerfectBinarySimplex.total (laurentProjection.app X) g⟩ :
      InputIdentitySeedUnitNodes.Node g) =
      ⟨_, sourceIso g ≪≫ (BoundedFlatPerfectBinarySimplex.first (laurentProjection.app X) g ≪≫
        BoundedFlatPerfectBinarySimplex.second (laurentProjection.app X) g)⟩
    rw [show BoundedFlatPerfectBinarySimplex.first (laurentProjection.app X) g ≪≫
        BoundedFlatPerfectBinarySimplex.second (laurentProjection.app X) g =
        BoundedFlatPerfectBinarySimplex.total (laurentProjection.app X) g from
      Iso.ext (BoundedFlatPerfectBinarySimplex.small_composite_hom _ _)]

/-- All three original old nodes shift using their actual geometric and normalization squares. -/
theorem old_shift (i : Fin 3) :
    reanchorNode (commonUnit g) (oldNodes g (Fin.castAdd 3 i)) =
      oldNodes g (Fin.natAdd 3 i) :=
  prism_shift _ _ _ _ _ _ _ _
    (UnitTrackPostcompSimplex.small_geometric_unit _ _ _)
    (UnitTrackPostcompSimplex.small_normalization_unit _ _ _) i

/-- All three original new nodes shift through the proved original source-unit square. -/
theorem new_shift (i : Fin 3) :
    reanchorNode (commonUnit g) (newNodes g (Fin.castAdd 3 i)) =
      newNodes g (Fin.natAdd 3 i) := by
  have h := anchor_square (commonUnit g) (sourceIso g)
    (UnitTrackPrecompSimplex.sourceUnit (laurentProjection.app X) g
      (laurentScalar (op X))) (source_unit_reference g)
    (newNativeNodes g (Fin.castAdd 3 i))
  exact h.trans (congrArg (reanchorNode (sourceIso g))
    (prism_shift _ _ _ _ _ _ _ _
      (UnitTrackPrecompSimplex.small_geometric_unit _ _ _)
      (UnitTrackPrecompSimplex.small_normalization_unit _ _ _) i))

/-- The original common unit transports all five lower full nodes to the five upper nodes. -/
theorem five_shift (i : Fin 5) :
    reanchorNode (commonUnit g) (nodes g (unitLowerFace.toOrderHom i)) =
      nodes g (unitShiftedFace.toOrderHom i) := by
  fin_cases i
  · exact old_shift g 0
  · exact old_shift g 1
  · exact old_shift g 2
  · exact new_shift g 1
  · exact new_shift g 2

/-- Each original shifted rectangle node is the prescribed full upper unit-pasting node. -/
theorem shifted_outer_nodes (i : Fin 5) :
    reanchorNode (commonUnit g) (InputDescSimplex.nodes g (rawOuterFace.toOrderHom i)) =
      nodes g (unitShiftedFace.toOrderHom i) := by
  rw [outer_nodes]
  exact five_shift g i

/-- The complete original outer word keeps both binary paths and its original half cut. -/
theorem raw_outer_word (s : I) : embed rawOuterFace (outerWord s) =
    BoundedFlatPerfectProjectionRectangleParameters.T
      BoundedFlatCoefficientBassH0Diagram.plusFace s :=
  map_trans_values (embed rawOuterFace) _ _ _ _
    (fun t ↦ map_binaryPath rawOuterFace 0 1 2 (unitInterval.symm t))
    (map_binaryPath rawOuterFace 0 3 4) s

/-- The lower word keeps its exact ordinary five-node face. -/
theorem unit_lower_word (s : I) : embed unitLowerFace (outerWord s) =
    (C0.symm.trans D0) s :=
  map_trans_values (embed unitLowerFace) _ _ _ _
    (fun t ↦ map_binaryPath unitLowerFace 0 1 2 (unitInterval.symm t))
    (map_binaryPath unitLowerFace 0 3 4) s

/-- The upper word keeps its separate unit-shifted five-node face. -/
theorem unit_shifted_word (s : I) : embed unitShiftedFace (outerWord s) =
    (C1.symm.trans D1) s :=
  map_trans_values (embed unitShiftedFace) _ _ _ _
    (fun t ↦ map_binaryPath unitShiftedFace 0 1 2 (unitInterval.symm t))
    (map_binaryPath unitShiftedFace 0 3 4) s

/-- The entire original ordinary movement equals the lower unit-pasting word in the nerve. -/
theorem outer_parameter (s : I) :
    parameter (laurentRef g) (InputDescSimplex.nodes g)
      (BoundedFlatPerfectProjectionRectangleParameters.T
        BoundedFlatCoefficientBassH0Diagram.plusFace s) =
    parameter (source g) (nodes g) ((C0.symm.trans D0) s) := by
  rw [← raw_outer_word, ← unit_lower_word]
  change parameter (laurentRef g) (InputDescSimplex.nodes g)
      (StdSimplex.map rawOuterFace.toOrderHom (outerWord s)) =
    parameter (source g) (nodes g)
      (StdSimplex.map unitLowerFace.toOrderHom (outerWord s))
  rw [parameter_face, parameter_face]
  exact congrArg (fun N : Fin 5 → CommonReferenceNerve.Node (laurentRef g) ↦
    parameter (laurentRef g) N (outerWord s)) (funext (outer_nodes g))

/-- The whole shifted movement retains the original common unit and unchanged path clocks. -/
theorem shifted_outer_parameter (s : I) :
    mapParameter (reanchorNode (commonUnit g))
      (parameter (laurentRef g) (InputDescSimplex.nodes g)
        (BoundedFlatPerfectProjectionRectangleParameters.T
        BoundedFlatCoefficientBassH0Diagram.plusFace s)) =
    parameter (source g) (nodes g) ((C1.symm.trans D1) s) := by
  rw [mapParameter_parameter, ← raw_outer_word, ← unit_shifted_word]
  change parameter (laurentRef g)
      (fun i ↦ reanchorNode (commonUnit g) (InputDescSimplex.nodes g i))
      (StdSimplex.map rawOuterFace.toOrderHom (outerWord s)) =
    parameter (source g) (nodes g)
      (StdSimplex.map unitShiftedFace.toOrderHom (outerWord s))
  rw [parameter_face, parameter_face]
  exact congrArg (fun N : Fin 5 → CommonReferenceNerve.Node (laurentRef g) ↦
    parameter (laurentRef g) N (outerWord s)) (funext (shifted_outer_nodes g))

/-- Ordinary old and new movement endpoints retain their entire reference nodes. -/
theorem ordinary_endpoints :
    InputDescSimplex.nodes g 2 = nodes g 2 ∧ InputDescSimplex.nodes g 26 = nodes g 4 :=
  ⟨outer_nodes g 2, outer_nodes g 4⟩

/-- The shifted endpoints are the distinct targets of the original V and W unit rails. -/
theorem shifted_endpoints :
    reanchorNode (commonUnit g) (InputDescSimplex.nodes g 2) = nodes g 7 ∧
      reanchorNode (commonUnit g) (InputDescSimplex.nodes g 26) = nodes g 9 :=
  ⟨shifted_outer_nodes g 2, shifted_outer_nodes g 4⟩

/-- The actual common unit changes reference parameters without changing any native value. -/
theorem shifted_native (n : ℕ) (y : |nerve (Codiscrete
    (CommonReferenceNerve.Node (laurentRef g)))|)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    pointwisePrespectrumFamily (laurentRef g) n
      (mapParameter (reanchorNode (commonUnit g)) y) x =
    pointwisePrespectrumFamily (laurentRef g) n y x :=
  pointwise_reanchor (commonUnit g) n y x

/-- The unchanged Laurent inclusion of the actual two-tip carrier. -/
def includeLaurent : C(|nerve (Codiscrete (CommonReferenceNerve.Node (laurentRef g)))|,
    Carrier g) :=
  CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)

/-- The entire ten-node original unit simplex enters the actual Laurent summand. -/
def unitMap : C(StdSimplex ℝ (Fin 10), Carrier g) :=
  (includeLaurent g).comp (parameter (source g) (nodes g))

/-- The complete original V rail joins the lower old node to its unit-shifted copy. -/
abbrev oldUnit := V.map (unitMap g).continuous

/-- The complete original W rail joins the lower new node to its unit-shifted copy. -/
abbrev newUnit := W.map (unitMap g).continuous

/-- The complete lower unit-pasting movement, with its literal original association. -/
abbrev lower := (C0.symm.trans D0).map (unitMap g).continuous

/-- The complete shifted unit-pasting movement through its separate reference nodes. -/
abbrev upper := (C1.symm.trans D1).map (unitMap g).continuous

/-- The whole ordinary rectangle movement agrees inside the actual carrier. -/
theorem lower_rail (s : I) : lower g s =
    includeLaurent g (parameter (laurentRef g) (InputDescSimplex.nodes g)
      (BoundedFlatPerfectProjectionRectangleParameters.T
        BoundedFlatCoefficientBassH0Diagram.plusFace s)) :=
  congrArg (includeLaurent g) (outer_parameter g s).symm

/-- The whole shifted rectangle movement agrees inside the actual carrier. -/
theorem upper_rail (s : I) : upper g s =
    includeLaurent g (mapParameter (reanchorNode (commonUnit g))
      (parameter (laurentRef g) (InputDescSimplex.nodes g)
        (BoundedFlatPerfectProjectionRectangleParameters.T
        BoundedFlatCoefficientBassH0Diagram.plusFace s))) :=
  congrArg (includeLaurent g) (shifted_outer_parameter g s).symm

/-- The entire unchanged original five-stage comparison, including its internal rotation. -/
def unitComparison : ((oldUnit g).trans (upper g)).Homotopy
    ((lower g).trans (newUnit g)) :=
  (InputIdentitySeedUnitLift.parameter.map (unitMap g)).cast
    (by simp only [Path.map_trans]) (by simp only [Path.map_trans])

/-- Mapping the old unit rail leaves its original parameter untouched. -/
theorem oldUnit_apply (s : I) : oldUnit g s = unitMap g (V s) := rfl

/-- Mapping the new unit rail leaves its original parameter untouched. -/
theorem newUnit_apply (s : I) : newUnit g s = unitMap g (W s) := rfl

/-- Neither coordinate of the original unit comparison is changed. -/
theorem unitComparison_apply (r s : I) : unitComparison g (r, s) =
    unitMap g (InputIdentitySeedUnitLift.parameter (r, s)) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedUnitSeams
