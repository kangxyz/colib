/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetLaurent
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed
public import Colib.RingTheory.KTheory.Bass.StrictUnderDiagram

/-!
# Original supported and ambient Bass seeds commute with support inclusion

The original support-forgetting natural arrow gives the actual four-corner Laurent square,
cone map and unchanged null cylinder. Together with the whole original scalar forget track,
these prove compatibility of the two constructed Bass seeds. No seed square is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual four support inclusions form the unchanged strict Laurent square map. -/
def boundedAboveFlatAffineSupportedSectionBassSquareForget (a : Under R) :
    boundedAboveFlatAffineSupportedSectionBassSquare j a ⟶
      boundedAboveFlatAffineSectionBassSquare a.right :=
  ((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum.{u+1})).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum.{u+1}).map
      (boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j))).app
        (laurentUnderSquare R a)

/-- The existing original mapping-cone functor gives the actual support-forgetting cone map. -/
def boundedAboveFlatAffineSupportedSectionBassConeForget (a : Under R) :
    boundedAboveFlatAffineSupportedSectionBassCone j a ⟶
      boundedAboveFlatAffineSectionBassCone a.right :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedAboveFlatAffineSupportedSectionBassSquareForget j a))

/-- The complete original null cylinder is preserved at the identical time. -/
theorem boundedAboveFlatAffineSupportedSectionBassNullHomotopy_forget_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedAboveFlatAffineSupportedSectionBassConeForget j a).map n
        ((boundedAboveFlatAffineSupportedSectionBassNullHomotopy j a).level n (t, x)) =
      (boundedAboveFlatAffineSectionBassNullHomotopy a.right).level n
        (t, (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedAboveFlatAffineSupportedSectionBassSquareForget j a) n t x

/-- The two genuinely constructed original seeds commute with actual support inclusion. -/
theorem boundedAboveFlatAffineSupportedSectionBassSeedMap_forget (a : Under R) :
    boundedAboveFlatAffineSupportedSectionBassSeedMap j a ≫
        parameterLoopingMap (boundedAboveFlatAffineSupportedSectionBassConeForget j a) =
      (boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j).app a ≫
        boundedAboveFlatAffineSectionBassSeedMap a.right := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare a.right))).map n
        ((boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap
          (inclusion j ((laurentUnderFunctor R).obj a))).map n
          ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare a.right))).map n
          ((boundedAboveFlatAffineSectionLaurentUnitHomotopy a.right).level n
            (t, (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap
              (inclusion j a)).map n x))
    rw [boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_forget_apply]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedAboveFlatAffineSupportedSectionBassNullHomotopy_forget_apply j a n t x

/-- The target seed is exactly the constructed ambient seed restricted along Under.forget. -/
def boundedAboveFlatAffineSectionBassUnderSeed (R : CommRingCat.{u}) :
    Under.forget R ⋙ boundedAboveFlatAffineSectionPrespectrumFunctor ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (Under.forget R ⋙ boundedAboveFlatAffineSectionPrespectrumFunctor) :=
  KTheory.Bass.strictRingDiagramUnderSeed R boundedAboveFlatAffineSectionBassSeed

section
attribute [local irreducible] boundedAboveFlatAffineSectionPrespectrumFunctor
  boundedAboveFlatAffineSupportedSectionPrespectrumFunctor
  boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation

/-- The existing Bass functor acts by the same actual looped support cone map. -/
theorem boundedAboveFlatAffineSupportedSectionBassForget_functor_app (a : Under R) :
    ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j)).app a ≍
      parameterLoopingMap (boundedAboveFlatAffineSupportedSectionBassConeForget j a) := HEq.rfl

/-- Restriction retains the unchanged ambient constructed seed at the actual algebra. -/
theorem boundedAboveFlatAffineSectionBassUnderSeed_app (a : Under R) :
    (boundedAboveFlatAffineSectionBassUnderSeed R).app a ≍
      boundedAboveFlatAffineSectionBassSeedMap a.right :=
  heq_of_eq <|
    (KTheory.Bass.strictRingDiagramUnderSeed_app R boundedAboveFlatAffineSectionBassSeed a).trans
    (boundedAboveFlatAffineSectionBassSeed_app a.right)

end

attribute [local irreducible] boundedAboveFlatAffineSectionPrespectrumFunctor
  boundedAboveFlatAffineSupportedSectionPrespectrumFunctor
attribute [local irreducible] boundedAboveFlatAffineSupportedSectionBassSeed
  boundedAboveFlatAffineSectionBassSeed boundedAboveFlatAffineSectionBassUnderSeed
  boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation

/-- The whole strict natural arrow respects the same two original seed transformations. -/
theorem boundedAboveFlatAffineSupportedSectionBassSeed_forget :
    boundedAboveFlatAffineSupportedSectionBassSeed j ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j) =
      boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
        boundedAboveFlatAffineSectionBassUnderSeed R := by
  apply NatTrans.ext
  funext a
  have hS :
      ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j)).obj a =
        parameterLooping (boundedAboveFlatAffineSupportedSectionBassCone j a) :=
    KTheory.Bass.strictDiagramFunctor_obj (laurentUnderSquareFunctor R)
      (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j) a
  have hT :
      ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (Under.forget R ⋙ boundedAboveFlatAffineSectionPrespectrumFunctor)).obj a =
        parameterLooping (boundedAboveFlatAffineSectionBassCone a.right) := by
    have h := congrArg
      (fun H ↦ (H.obj boundedAboveFlatAffineSectionPrespectrumFunctor).obj a)
      (KTheory.Bass.strictRingDiagramRestriction_comp_bass R)
    exact h.trans (KTheory.Bass.strictDiagramFunctor_obj
      laurentSquareFunctor boundedAboveFlatAffineSectionPrespectrumFunctor a.right)
  apply eq_of_heq
  have hleft := CategoryTheory.heq_comp rfl hS hT
    (heq_of_eq (boundedAboveFlatAffineSupportedSectionBassSeed_app j a))
    (boundedAboveFlatAffineSupportedSectionBassForget_functor_app j a)
  have hright := CategoryTheory.heq_comp rfl rfl hT
    (HEq.refl ((boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j).app a))
    (boundedAboveFlatAffineSectionBassUnderSeed_app (R := R) a)
  exact hleft.trans
    ((heq_of_eq (boundedAboveFlatAffineSupportedSectionBassSeedMap_forget j a)).trans hright.symm)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SupportedSectionForgetSeed.lean:34-129"
  "adaptation" "Actual support-forgetting Laurent seed square toward ambient cocartesian sections"]
  boundedAboveFlatAffineSupportedSectionBassSeed_forget
  boundedAboveFlatAffineSupportedSectionBassSeedMap_forget
  boundedAboveFlatAffineSupportedSectionBassNullHomotopy_forget_apply

attribute [colib_tag "COL-0503"]
  boundedAboveFlatAffineSupportedSectionBassSeed_forget
  boundedAboveFlatAffineSupportedSectionBassSeedMap_forget
  boundedAboveFlatAffineSupportedSectionBassNullHomotopy_forget_apply

end AlgebraicGeometry.Scheme.Modules
