/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNormalizedRowPresentation
public import Colib.Topology.Prespectrum.ZigzagSequentializationTelescopeNull

/-! # The prescribed auxiliary full null on the normalized tensor-row presentation

The whole original finite nulls act on both vertex families. Their proved forward and
backward time squares descend through the canonical zigzag telescope, retaining its cylinders.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open GeometricSeedCospan ModelRowZigzagSequentialization
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
  (X : Scheme.{u}ᵒᵖ)
local notation "E0" => vertex squareFunctor (fiber f T) X
local notation "V0" => target squareFunctor (fiber f T) X
local notation "a0" => (fun i => SchemeModelRowSeed.normalizedBoundary (fiber f T)
  (supportedUnit (Scheme.Opens.ι (unionOpen f T)))
  (supportedUnit_naturality (Scheme.Opens.ι (unionOpen f T))) i X)
local notation "b0" => backward squareFunctor (fiber f T) X
local notation "E1" => vertex squareFunctor (ambient T) X
local notation "V1" => target squareFunctor (ambient T) X
local notation "a1" => (fun i => SchemeModelRowSeed.normalizedBoundary (ambient T) (supportedUnit
    (Scheme.Opens.ι T))
  (supportedUnit_naturality (Scheme.Opens.ι T)) i X)
local notation "b1" => backward squareFunctor (ambient T) X
local notation "E2" => vertex squareFunctor (openModel f T) X
local notation "V2" => target squareFunctor (openModel f T) X
local notation "a2" => (fun i => SchemeModelRowSeed.normalizedBoundary (openModel f T)
  (supportedUnit (Scheme.Opens.ι (inverseOpen f T)))
  (supportedUnit_naturality (Scheme.Opens.ι (inverseOpen f T))) i X)
local notation "b2" => backward squareFunctor (openModel f T) X
local notation "d01" => (fun i => SchemeModelRowSeed.stageInput
  (fiber f T) (ambient T) (enlargement f T) i X)
local notation "d12" => (fun i => SchemeModelRowSeed.stageInput
  (ambient T) (openModel f T) (restriction f T) i X)
local notation "v01" => (fun i => SchemeModelRowSeed.targetInput
  (fiber f T) (ambient T) (enlargement f T) i X)
local notation "v12" => (fun i => SchemeModelRowSeed.targetInput
  (ambient T) (openModel f T) (restriction f T) i X)

local notation "hb01" => (fun i =>
  SchemeModelRowSeed.input_backward_square (fiber f T) (ambient T) (enlargement f T) i X)
local notation "hd01" => (fun i =>
  SchemeModelRowSeed.input_current_square (fiber f T) (supportedUnit (Scheme.Opens.ι
    (unionOpen f T)))
    (supportedUnit_naturality (Scheme.Opens.ι (unionOpen f T))) (ambient T) (supportedUnit
    (Scheme.Opens.ι T))
    (supportedUnit_naturality (Scheme.Opens.ι T)) (enlargement f T) (supportedMap_unit
    (enlargementPair f T)) i X)
local notation "ha01" => (fun i => SchemeModelRowSeed.normalizedInput_forward
  (fiber f T) (supportedUnit (Scheme.Opens.ι (unionOpen f T)))
  (supportedUnit_naturality (Scheme.Opens.ι (unionOpen f T)))
  (ambient T) (supportedUnit (Scheme.Opens.ι T)) (supportedUnit_naturality (Scheme.Opens.ι T))
  (enlargement f T) (supportedMap_unit (enlargementPair f T)) i X)
local notation "hb12" => (fun i =>
  SchemeModelRowSeed.input_backward_square (ambient T) (openModel f T) (restriction f T) i X)
local notation "hd12" => (fun i =>
  SchemeModelRowSeed.input_current_square (ambient T) (supportedUnit (Scheme.Opens.ι T))
    (supportedUnit_naturality (Scheme.Opens.ι T)) (openModel f T) (supportedUnit
    (Scheme.Opens.ι (inverseOpen f T)))
    (supportedUnit_naturality (Scheme.Opens.ι (inverseOpen f T))) (restriction f T)
    (supportedMap_unit (supportRestrictionPair f T)) i X)
local notation "ha12" => (fun i => SchemeModelRowSeed.normalizedInput_forward
  (ambient T) (supportedUnit (Scheme.Opens.ι T)) (supportedUnit_naturality (Scheme.Opens.ι T))
  (openModel f T) (supportedUnit (Scheme.Opens.ι (inverseOpen f T)))
  (supportedUnit_naturality (Scheme.Opens.ι (inverseOpen f T)))
  (restriction f T) (supportedMap_unit (supportRestrictionPair f T)) i X)

/-- The actual composite vertex map is the original enlargement followed by restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:89"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def normalizedPresentationVertexComposite (i : ℕ) := d01 i ≫ d12 i

/-- The target composite uses the actual proper-row input maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:92"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def normalizedPresentationTargetComposite (i : ℕ) := v01 i ≫ v12 i

/-- Whole forward compatibility specializes to the original composite input square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:95"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationForwardComposite_square (i : ℕ) :
    a0 i ≫ normalizedPresentationTargetComposite f T X i =
      normalizedPresentationVertexComposite f T X i ≫ a2 i := by
  change a0 i ≫ (v01 i ≫ v12 i) = (d01 i ≫ d12 i) ≫ a2 i
  rw [← Category.assoc, ha01 i, Category.assoc, ha12 i, ← Category.assoc]

/-- Whole backward compatibility specializes to the original composite input square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:102"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationBackwardComposite_square (i : ℕ) :
    b0 i ≫ normalizedPresentationTargetComposite f T X i =
      normalizedPresentationVertexComposite f T X (i + 1) ≫ b2 i := by
  have h := (fullTargetNull_backward_at f T i X 0).symm
  rw [fullTargetNull_at_zero, Homotopy.at_zero_eq] at h
  exact h

/-- The original full-null value commutes with each independent forward leg. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:110"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationNull_forward (i n : ℕ) (r : unitInterval) (x : (E0 i).space n) :
    (fullTargetInputNull f T i X).level n (r, (a0 i).map n x) =
      (a2 i).map n
        (((strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X).level n (r, x)) :=
  by
    change (fullTargetNull f T i X).level n (r, (a0 i).map n x) = _
    have h := fullNull_normalizedBoundaryHomotopy f T i X n r 0 x
    simpa only [Homotopy.at_zero] using h

/-- The original full-null value commutes with each actual backward leg. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:120"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationNull_backward (i n : ℕ) (r : unitInterval) (x : (E0
    (i + 1)).space n) :
    (fullTargetInputNull f T i X).level n (r, (b0 i).map n x) =
      (b2 i).map n
        (((strictDiagramIterateNull squareFunctor (fullNull f T) (i + 1)).homotopy X).level n
          (r, x)) :=
  congrArg (fun g => g.map n x) (fullTargetNull_backward_at f T i X r).symm

/-- The same prescribed full null descends to the actual zigzag telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:129"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def normalizedPresentationNullRaw :=
  ZigzagSequentialization.inducedTelescopeNullhomotopy
    E0 V0 a0 b0 E2 V2 a2 b2
    (normalizedPresentationVertexComposite f T X) (normalizedPresentationTargetComposite f T X)
    (normalizedPresentationForwardComposite_square f T X)
    (normalizedPresentationBackwardComposite_square f T X)
    (fun i => (strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X)
    (fun i => fullTargetInputNull f T i X)
    (normalizedPresentationNull_forward f T X) (normalizedPresentationNull_backward f T X)

/-- The original full null has the two actual presentation maps as its literal source. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:140"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def normalizedPresentationNull : Homotopy
    (normalizedPresentationEnlargement f T X ≫ normalizedPresentationRestriction f T X)
    (zeroHom (normalizedFiberPresentation f T X) (normalizedOpenPresentation f T X)) :=
  (normalizedPresentationNullRaw f T X).cast
    (ZigzagSequentialization.inducedTelescopeMap_comp
      E0 V0 a0 b0 E1 V1 a1 b1 d01 v01 ha01 hb01 E2 V2 a2 b2 d12 v12 ha12 hb12).symm rfl

/-- Endpoint casts preserve all values of the original descended null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:148"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationNull_level (n : ℕ) :
    (normalizedPresentationNull f T X).level n =
    (normalizedPresentationNullRaw f T X).level n := rfl

/-- The actual recursive stage null retains the original vertex and proper-target families. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:153"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def normalizedPresentationStageNull (i : ℕ) :=
  ZigzagSequentialization.stageHomotopy E0 V0 a0 b0 E2 V2 a2 b2
    (normalizedPresentationVertexComposite f T X) (fun j => zeroHom (E0 j) (E2 j))
    (normalizedPresentationTargetComposite f T X) (fun j => zeroHom (V0 j) (V2 j))
    (normalizedPresentationForwardComposite_square f T X)
    (normalizedPresentationBackwardComposite_square f T X)
    (fun j => by apply Topology.LoopPrespectrum.Hom.ext; funext k; ext _x; exact (a2
      j).map_point k |>.symm)
    (fun j => by apply Topology.LoopPrespectrum.Hom.ext; funext k; ext _x; exact (b2
      j).map_point k |>.symm)
    (fun j => (strictDiagramIterateNull squareFunctor (fullNull f T) j).homotopy X)
    (fun j => fullTargetInputNull f T j X)
    (normalizedPresentationNull_forward f T X) (normalizedPresentationNull_backward f T X) i

/-- The original null time and telescope-cylinder height remain independent and unchanged. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:166"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationNull_cylinder (n i : ℕ) (r s : unitInterval)
    (x : (ZigzagSequentialization.stage E0 V0 a0 b0 i).space n) :
    (normalizedPresentationNull f T X).level n
      (r, Telescope.cylinder (ZigzagSequentialization.stage E0 V0 a0 b0)
        (ZigzagSequentialization.transition E0 V0 a0 b0) n i (s, x)) =
      Telescope.cylinder (ZigzagSequentialization.stage E2 V2 a2 b2)
        (ZigzagSequentialization.transition E2 V2 a2 b2) n i
        (s, (normalizedPresentationStageNull f T X i).level n (r, x)) := rfl

/-- The genuine current comparison preserves the prescribed whole null at its original time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryNormalizedRowP\
    resentationNull.lean:176"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedPresentationNull_comparison (n : ℕ) (r : unitInterval)
    (x : ((SchemeNaturalSeed.currentTelescope (fiberAction f T)).obj X).space n) :
    (normalizedOpenPresentationComparison f T X).map n
        (((currentNull f T).homotopy X).level n (r, x)) =
      (normalizedPresentationNull f T X).level n
        (r, (normalizedFiberPresentationComparison f T X).map n x) := by
  let hF := SchemeNaturalSeed.currentNull_transition (fiberAction f T) (openAction f T)
    (firstMap f T) (secondMap f T) (fullNull f T) (timeSlice_equivariant f T)
  exact (ZigzagSequentialization.telescopeMap_homotopy
    E0 V0 a0 b0 E2 V2 a2 b2
    (normalizedPresentationVertexComposite f T X) (fun i => zeroHom (E0 i) (E2 i))
    (normalizedPresentationTargetComposite f T X) (fun i => zeroHom (V0 i) (V2 i))
    (normalizedPresentationForwardComposite_square f T X)
    (normalizedPresentationBackwardComposite_square f T X)
    (fun i => by apply Topology.LoopPrespectrum.Hom.ext; funext k; ext _x; exact (a2
      i).map_point k |>.symm)
    (fun i => by apply Topology.LoopPrespectrum.Hom.ext; funext k; ext _x; exact (b2
      i).map_point k |>.symm)
    (fun i => (strictDiagramIterateNull squareFunctor (fullNull f T) i).homotopy X)
    (fun i => fullTargetInputNull f T i X)
    (normalizedPresentationNull_forward f T X) (normalizedPresentationNull_backward f T X)
    (fun i => (SchemeNaturalSeed.currentTransition (fiberAction f T) i).app X)
    (fun i => (SchemeNaturalSeed.currentTransition (openAction f T) i).app X)
    (fun i => SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy (fiber f T)
      (supportedUnit (Scheme.Opens.ι (unionOpen f T))) (supportedUnit_naturality
    (Scheme.Opens.ι (unionOpen f T))) i X)
    (fun i => SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy (openModel f T)
      (supportedUnit (Scheme.Opens.ι (inverseOpen f T))) (supportedUnit_naturality
    (Scheme.Opens.ι (inverseOpen f T))) i X)
    (fun i k t s y => fullNull_normalizedBoundaryHomotopy f T i X k t s y)
    (fun i => by
      have h := (fullNull_current_at f T i X 0).symm
      rw [Homotopy.at_zero_eq, Homotopy.at_zero_eq] at h
      exact h)
    (fun i => by
      apply Topology.LoopPrespectrum.Hom.ext
      funext k
      ext y
      exact ((SchemeNaturalSeed.currentTransition (openAction f T) i).app X).map_point k)
    (fun i k t y => hF i X k t y) n r x).symm

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
