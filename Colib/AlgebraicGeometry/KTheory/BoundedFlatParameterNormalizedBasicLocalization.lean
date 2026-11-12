/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicDiagram
public import Colib.Topology.Prespectrum.FiberLiftConnecting

/-!
# The actual basic normalized-row localization and its intrinsic boundary

The source consists of complexes acyclic on U, hence supported in its complement.
The middle and open objects are the actual ambient normalized rows. The actual
empty-open forget maps and original whole null transport the auxiliary fiber lift.
The basic boundary is defined from its own path-space fiber lift.
-/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Products
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
open GlobalSupportedSection GlobalSectionChangeIndex ParameterAuxiliarySupport
open ParameterAuxiliaryNormalizedRowLocalization
variable (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ)

/-- The displayed basic maps and their prescribed whole null define the actual path-space lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedBasicLocaliza\
    tion.lean:35"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def basicLift := homotopyFiberLift (restriction U.ι X)
  (ParameterTensorNormalizedRowPresentation.forget U.ι X) (basicNull Q U X)

/-- The actual empty-open forget maps preserve the whole original auxiliary path-space lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedBasicLocaliza\
    tion.lean:39"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem auxiliary_basic_lift_square :
    ParameterAuxiliaryNormalizedRowLocalization.normalizedPresentationLift U.ι ⊥ X ≫
      homotopyFiberMap (Arrow.homMk
        (f := Arrow.mk (normalizedPresentationRestriction U.ι ⊥ X))
        (g := Arrow.mk (restriction U.ι X))
        (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι X)
        (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι X)
        (restriction_forget U.ι ⊥ X).symm) =
      (basicSourceIso Q U X).hom ≫ basicLift Q U X :=
  homotopyFiberLift_naturality
    (normalizedPresentationEnlargement U.ι ⊥ X) (normalizedPresentationRestriction U.ι ⊥ X)
    (ParameterTensorNormalizedRowPresentation.forget U.ι X) (restriction U.ι X)
    (normalizedPresentationNull U.ι ⊥ X) (basicNull Q U X)
    (basicSourceIso Q U X).hom
    (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι X)
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι X)
    ((enlargement_forget U.ι ⊥ X).trans (basicSourceIso_forget Q U X).symm)
    (restriction_forget U.ι ⊥ X).symm (basicNull_comparison Q U X)

/-- Actual empty-open forget equivalences detect the same basic localization lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedBasicLocaliza\
    tion.lean:59"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem auxiliary_basic_lift_stable_iff :
    IsStableEquivalence
        (ParameterAuxiliaryNormalizedRowLocalization.normalizedPresentationLift U.ι ⊥ X) ↔
      IsStableEquivalence (basicLift Q U X) := by
  have : IsEmpty (inverseOpen U.ι (⊥ : Q.Opens)).toScheme := by
    rw [inverseOpen_bottom]
    infer_instance
  exact homotopyFiberLift_isStableEquivalence_iff
    (normalizedPresentationEnlargement U.ι ⊥ X) (normalizedPresentationRestriction U.ι ⊥ X)
    (ParameterTensorNormalizedRowPresentation.forget U.ι X) (restriction U.ι X)
    (normalizedPresentationNull U.ι ⊥ X) (basicNull Q U X)
    (basicSourceIso Q U X).hom
    (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι X)
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι X)
    ((enlargement_forget U.ι ⊥ X).trans (basicSourceIso_forget Q U X).symm)
    (restriction_forget U.ι ⊥ X).symm (basicNull_comparison Q U X)
    (fun d => by infer_instance)
    (ParameterTensorNormalizedRowPresentation.bottom_forget_stable Q X)
    (ParameterTensorNormalizedRowPresentation.forget_stable_of_isEmpty _ X)

/-- The actual basic normalized lift is stable under the original qcqs and compact-open hypotheses.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedBasicLocaliza\
    tion.lean:81"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem basicLift_integer_isStableEquivalence
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] :
    IsStableEquivalence (basicLift Q U (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) :=
  (auxiliary_basic_lift_stable_iff Q U (op (Spec (CommRingCat.of (ULift.{u} ℤ))))).mp
    (normalizedPresentationLift_integer_isStableEquivalence
      U.ι ⊥)

/-- Its boundary is defined from the actual basic fiber lift in each original signed degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedBasicLocaliza\
    tion.lean:89"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def basicConnecting [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] (d : ℤ) :
    stableHomotopyGroup (ParameterTensorNormalizedRowPresentation.ambient U.toScheme
      (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) (d + 1) ⟶
    stableHomotopyGroup (ParameterTensorNormalizedRowPresentation.supported U.ι
      (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (restriction U.ι (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
        (ParameterTensorNormalizedRowPresentation.forget U.ι (op (Spec (CommRingCat.of
          (ULift.{u} ℤ)))))
        (basicNull Q U (op (Spec (CommRingCat.of (ULift.{u} ℤ))))))) :=
    basicLift_integer_isStableEquivalence Q U d
  exact stableFiberLiftConnecting
    (ParameterTensorNormalizedRowPresentation.forget U.ι (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
    (restriction U.ι (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) (basicNull Q U (op (Spec
      (CommRingCat.of (ULift.{u} ℤ))))) d

/-- The intrinsic basic signed boundary retains the original auxiliary null and source cast. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedBasicLocaliza\
    tion.lean:104"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem auxiliary_basic_connecting [CompactSpace Q] [QuasiSeparatedSpace Q]
    [CompactSpace U] (d : ℤ) :
    letI : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (normalizedPresentationRestriction U.ι ⊥ (op (Spec (CommRingCat.of
        (ULift.{u} ℤ)))))
        (normalizedPresentationEnlargement U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
        (normalizedPresentationNull U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ))))))) :=
        normalizedPresentationLift_integer_isStableEquivalence U.ι ⊥ d;
    stableFiberLiftConnecting
        (normalizedPresentationEnlargement U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
        (normalizedPresentationRestriction U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
        (normalizedPresentationNull U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) d ≫
      (stableHomotopyFunctor d).map (basicSourceIso Q U (op (Spec (CommRingCat.of (ULift.{u}
        ℤ))))).hom =
    (stableHomotopyFunctor (d + 1)).map
        (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι
          (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) ≫ basicConnecting Q U d := by
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (normalizedPresentationRestriction U.ι ⊥ (op (Spec (CommRingCat.of
        (ULift.{u} ℤ)))))
        (normalizedPresentationEnlargement U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
        (normalizedPresentationNull U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ))))))) :=
    normalizedPresentationLift_integer_isStableEquivalence U.ι ⊥ d
  have : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift (restriction U.ι (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
        (ParameterTensorNormalizedRowPresentation.forget U.ι (op (Spec (CommRingCat.of
          (ULift.{u} ℤ)))))
        (basicNull Q U (op (Spec (CommRingCat.of (ULift.{u} ℤ))))))) :=
    basicLift_integer_isStableEquivalence Q U d
  exact stableFiberLiftConnecting_naturality
    (normalizedPresentationEnlargement U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
    (normalizedPresentationRestriction U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
    (ParameterTensorNormalizedRowPresentation.forget U.ι (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
    (restriction U.ι (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
    (normalizedPresentationNull U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) (basicNull Q
      U (op (Spec (CommRingCat.of (ULift.{u} ℤ)))))
    (basicSourceIso Q U (op (Spec (CommRingCat.of (ULift.{u} ℤ))))).hom
    (ParameterTensorNormalizedRowPresentation.forget (⊥ : Q.Opens).ι (op (Spec (CommRingCat.of
      (ULift.{u} ℤ)))))
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι (op (Spec
      (CommRingCat.of (ULift.{u} ℤ)))))
    ((enlargement_forget U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ))))).trans
      (basicSourceIso_forget Q U (op (Spec (CommRingCat.of (ULift.{u} ℤ))))).symm)
    (restriction_forget U.ι ⊥ (op (Spec (CommRingCat.of (ULift.{u} ℤ))))).symm
    (basicNull_comparison Q U (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) d

end AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
