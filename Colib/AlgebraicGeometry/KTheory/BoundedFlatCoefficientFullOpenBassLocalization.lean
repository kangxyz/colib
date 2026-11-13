/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStable

/-!
# Constructed global native full-open section-completion localization

The original supported telescope cone compares to the actual fine full-open section
telescope by composing its constructed coarse comparison with the unchanged stable
restriction. The same postcomposed whole null supplies the original fiber lift and signed
boundary. This is localization for these constructed section-completion objects; classical
nonconnective K-theory identification and completed geometric evaluation remain separate.
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
  [IsOpenImmersion f.left]

/-- The original ambient-to-open map followed by the same full-open telescope restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:33"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
def boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen :
    boundedAboveFlatCoefficientAmbientBassTelescopeFunctor Q ⟶
      boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f :=
  boundedAboveFlatCoefficientAmbientBassTelescopeOpen f ≫
    boundedAboveFlatCoefficientOpenBassTelescopeRestriction f

/-- The finite composite is exactly the iterate of original native section restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:40"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientAmbientBassFullOpen_eq_original (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassOpen f i ≫
      boundedAboveFlatCoefficientOpenBassRestriction f i =
      (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight (boundedAboveFlatCoefficientSectionModelRestriction f)
          prespectrumFunctor) := by
  have hM : boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f ≫
      boundedAboveFlatCoefficientOpenRestrictionModelTransformation f =
    boundedAboveFlatCoefficientSectionModelRestriction f := by
    apply NatTrans.ext
    funext a
    apply WideSubcategory.hom_ext
    apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
    change 𝟭 _ ⋙ boundedAboveFlatCoefficientOpenRestriction f a =
      boundedAboveFlatCoefficientSectionsMap (i := (Opposite.op Q, a)) (k := (Opposite.op P, a))
        (f.op, 𝟙 a)
    exact Functor.id_comp _
  have h : boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f ≫
      boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f =
    Functor.whiskerRight (boundedAboveFlatCoefficientSectionModelRestriction f) prespectrumFunctor
      := by
    apply NatTrans.ext
    funext a
    exact (prespectrumFunctor.map_comp _ _).symm.trans
      (congrArg prespectrumFunctor.map (NatTrans.congr_app hM a))
  exact ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map_comp _ _).symm.trans
    (congrArg ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map) h)

/-- Every actual ambient finite inclusion retains the original native restriction component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:66"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientAmbientBassTelescopeInclusion_fullOpen (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassTelescopeInclusion Q i ≫
        boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f =
      (boundedAboveFlatCoefficientAmbientBassOpen f i ≫
        boundedAboveFlatCoefficientOpenBassRestriction f i) ≫
        boundedAboveFlatCoefficientFullOpenBassTelescopeInclusion f i := by
  dsimp only [boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen]
  rw [← Category.assoc, boundedAboveFlatCoefficientAmbientBassTelescopeInclusion_open,
    Category.assoc, boundedAboveFlatCoefficientOpenBassTelescopeInclusion_restriction, ←
      Category.assoc]

/-- Postcompose the same supported localization null with the original fine restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:76"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
def boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedBassTelescopeForget f)
      (boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f) where
  homotopy a :=
    (((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).postcomp
      ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a)).cast
        (Category.assoc _ _ _)
        (by
          apply Topology.LoopPrespectrum.Hom.ext
          funext m
          ext x
          exact ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a).map_point m)
  naturality {a b} g m s x := by
    change ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).map g).map m
        (((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a).map m
          (((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m
            (s, x))) =
      ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app b).map m
        (((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy b).level m
          (s, ((boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f).map g).map m x))
    exact (congrArg (fun g ↦ g.map m
      (((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m (s, x)))
      ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).naturality g)).symm.trans
        (congrArg (fun y ↦
          ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app b).map m y)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).naturality g m s x))

/-- Every postcomposed null value retains its original time and the same restriction map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:104"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull_level
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a).level m (s, x) =
      ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a).map m
        (((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m (s,
          x)) :=
  rfl

/-- The actual supported cone comparison lands in the constructed fine full-open telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:113"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
def boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedBassTelescopeForget f) ⟶
      boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f :=
  boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap f ≫
    boundedAboveFlatCoefficientOpenBassTelescopeRestriction f

/-- The composite is exactly the original cone descent for the same postcomposed whole null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:120"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc (a : Under R) :
    (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a =
      mappingConeDesc ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a) := by
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
    CoefficientFullOpenBassLocalization.lean:134"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a) ≫
        (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a =
      (boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a := by
  rw [boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeInclusion_desc _ _ _

/-- Cone time and original supported telescope height retain the same finite native restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:142"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a).map m
      (Topology.ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f).obj a).point m)
        (((boundedAboveFlatCoefficientAmbientBassTelescopeFunctor Q).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a).map m)
        (s, Telescope.cylinder
          (fun n ↦ (boundedAboveFlatCoefficientSupportedBassDiagram f n).obj a)
          (fun n ↦ (boundedAboveFlatCoefficientSupportedBassTransition f n).app a) m i (t, x))) =
      Telescope.cylinder (fun n ↦ (boundedAboveFlatCoefficientFullOpenBassDiagram f n).obj a)
        (fun n ↦ (boundedAboveFlatCoefficientFullOpenBassTransition f n).app a) m i
          (t, ((boundedAboveFlatCoefficientOpenBassRestriction f i).app a).map m
            (((boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a).level m (s, x)))
              := rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The supported telescope cone and fine full-open completion agree in every signed degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:161"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app
      a) :=
  (boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_isStableEquivalence f a).comp
    (boundedAboveFlatCoefficientOpenBassTelescopeRestriction_isStableEquivalence f a)

/-- The original supported class maps to the fiber by the same constructed whole null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:168"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
def boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap (a : Under R) :
    (boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f).obj a ⟶
      homotopyFiber ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a) :=
  homotopyFiberLift ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] in
/-- Projection from the same whole-null fiber lift is precisely original support forgetting. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:177"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_projection (a : Under R) :
    boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a ≫
        homotopyFiberProjection ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app
          a) =
      (boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a :=
  homotopyFiberLift_projection _ _ _

/-- This actual supported fiber comparison is stable in every original integer degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:184"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a)
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc f a) ▸
      boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a)

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] in
/-- The original signed connecting map agrees through this same whole-null fiber comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientFullOpenBassLocalization.lean:194"
  "adaptation" "Original ordinary full-open cone and same-null fiber localization."]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a) ≫
      stableFiberConnecting ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a) d =
    stableMappingConeConnecting ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
      (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a)
        d ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a) := by
  rw [boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc]
  exact mappingConeDesc_connecting _ _ _
    (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d

end AlgebraicGeometry.Scheme.Modules


namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0596"]
  boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence

attribute [colib_tag "COL-0596"]
  boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence

attribute [colib_tag "COL-0596"]
  boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_projection

attribute [colib_tag "COL-0596"]
  boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_connecting

end AlgebraicGeometry.Scheme.Modules
