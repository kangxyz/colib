/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedBassTelescope


/-!
# Auxiliary-supported global native full-open section-completion localization

The original auxiliary fiber is supported on the complement of the union of
auxiliary open support and the actual open immersion range. Its constructed
native telescope cone compares to the fine full-open supported section telescope
through the same coarse comparison and the original stable restriction. The
same postcomposed whole null gives the actual fiber lift and the signed boundary.
This result concerns these section-completion objects; identification with
classical nonconnective K-theory remains separate.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory Topology AlgebraicGeometry Topology.LoopPrespectrum
open KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original supported restriction with the actual fine source and target structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:35"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
def boundedAboveFlatCoefficientSupportedFineRestrictionModelMap (a : Under R) :
    boundedAboveFlatCoefficientSupportedAmbientModel T a ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModel f T a :=
  ⟨⟨boundedAboveFlatCoefficientSupportedOpenRestriction f T a,
      boundedAboveFlatCoefficientSupportedOpenRestriction_fine_exact f T a⟩,
    (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a).property⟩

/-- Fine-supported native restriction is natural through the original coefficient squares. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:43"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
def boundedAboveFlatCoefficientSupportedFineRestrictionModelTransformation :
    boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T where
  app := boundedAboveFlatCoefficientSupportedFineRestrictionModelMap f T
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
    exact boundedAboveFlatCoefficientSupportedOpenRestriction_square f T g

/-- The original ambient-to-open map followed by the same full-open telescope restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:52"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
def boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen :
    boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor T ⟶
      boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T ≫
    boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T

omit [IsOpenImmersion f.left] in
/-- The finite composite is exactly the iterate of original native section restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:60"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedAmbientBassFullOpen_eq_original (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i ≫
      boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i =
      (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight
          (boundedAboveFlatCoefficientSupportedFineRestrictionModelTransformation f T)
          prespectrumFunctor) := by
  have hM : boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T ≫
      boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T =
    boundedAboveFlatCoefficientSupportedFineRestrictionModelTransformation f T := by
    apply NatTrans.ext
    funext a
    apply WideSubcategory.hom_ext
    apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
    change 𝟭 _ ⋙ boundedAboveFlatCoefficientSupportedOpenRestriction f T a =
      boundedAboveFlatCoefficientSupportedOpenRestriction f T a
    exact Functor.id_comp _
  have h : boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T ≫
      boundedAboveFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T =
    Functor.whiskerRight (boundedAboveFlatCoefficientSupportedFineRestrictionModelTransformation f
      T)
      prespectrumFunctor := by
    apply NatTrans.ext
    funext a
    exact (prespectrumFunctor.map_comp _ _).symm.trans
      (congrArg prespectrumFunctor.map (NatTrans.congr_app hM a))
  exact ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map_comp _ _).symm.trans
    (congrArg ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map) h)

omit [IsOpenImmersion f.left] in
/-- Every actual ambient finite inclusion retains the original native restriction component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:89"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion_fullOpen (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T =
      (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i) ≫
        boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i := by
  dsimp only [boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen]
  rw [← Category.assoc, boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion_open,
    Category.assoc, boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion_restriction,
    ← Category.assoc]

/-- Postcompose the same supported localization null with the original fine restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:101"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
def boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T)
      (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T) where
  homotopy a :=
    (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).postcomp
      ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)).cast
        (Category.assoc _ _ _)
        (by
          apply Topology.LoopPrespectrum.Hom.ext
          funext m
          ext x
          exact ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app
            a).map_point
            m)
  naturality {a b} g m s x := by
    change ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).map g).map m
        (((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a).map m
          (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
            (s, x))) =
      ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app b).map m
        (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy b).level m
          (s, ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).map g).map m x))
    exact (congrArg (fun g ↦ g.map m
      (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
        (s, x)))
      ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).naturality
        g)).symm.trans
        (congrArg (fun y ↦
          ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app b).map m y)
          ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).naturality g m s x))

/-- Every postcomposed null value retains its original time and the same restriction map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:130"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull_level
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level m
        (s, x) =
      ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a).map m
        (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
          (s, x)) :=
  rfl

/-- The actual supported cone comparison lands in the constructed fine full-open telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:141"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
def boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T) ⟶
      boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T ≫
    boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T

/-- The composite is exactly the original cone descent for the same postcomposed whole null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:148"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc (a : Under
  R) :
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a =
      mappingConeDesc ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a) := by
  apply mappingCone_hom_ext
  · apply Topology.LoopPrespectrum.Hom.ext
    funext m
    ext x
    rfl
  · intro m s x
    rfl

/-- The original ambient inclusion face is the actual fine full-open restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:162"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_inclusion (a : Under
  R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app
      a) ≫
        (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a =
      (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a := by
  rw [boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeInclusion_desc _ _ _

/-- Cone time and original supported telescope height retain the same finite native restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:170"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a).map m
      (Topology.ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor T).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a).map m)
        (s, Telescope.cylinder
          (fun n ↦ (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T n).obj a)
          (fun n ↦ (boundedAboveFlatCoefficientSupportedFiberBassTransition f T n).app a) m i (t,
            x))) =
      Telescope.cylinder (fun n ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T
        n).obj a)
        (fun n ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T n).app a) m i
          (t, ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a).map m
            (((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m
              (s, x))) := rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T]

/-- The supported telescope cone and fine full-open completion agree in every signed degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:191"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a) :=
  (boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_isStableEquivalence f T a).comp
    (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction_isStableEquivalence f T a)

/-- The original supported class maps to the fiber by the same constructed whole null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:199"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
def boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap (a : Under R) :
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a ⟶
      homotopyFiber ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        :=
  homotopyFiberLift ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a)

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T] in
/-- Projection from the same whole-null fiber lift is precisely original support forgetting. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:209"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_projection (a :
  Under R) :
    boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a ≫
        homotopyFiberProjection
          ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) =
      (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a :=
  homotopyFiberLift_projection _ _ _

/-- This actual supported fiber comparison is stable in every original integer degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:217"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f
      T a) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f
      T a)
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc f T a) ▸
      boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence f
        T a)

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
  [CompactSpace T] in
/-- The original signed connecting map agrees through this same whole-null fiber comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFullOpenBassLocalization.lean:228"
  "adaptation" "Actual auxiliary full-open completion and the same postcomposed whole null"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a) ≫
      stableFiberConnecting
          ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) d =
    stableMappingConeConnecting
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
      (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence
        f T a)
        d ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a) := by
  rw [boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeDesc_connecting _ _ _
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f
      T a) d

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0590"]
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence

attribute [colib_tag "COL-0590"]
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_projection

attribute [colib_tag "COL-0590"]
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules
