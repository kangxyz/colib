/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicSource
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedBasicSpec
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryBasicConnecting

/-!
Source:
Quillen source module
`AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterNormalizedBasicCurrentBoundary.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The intrinsic basic normalized boundary preserves the original current boundary

The comparison follows the actual auxiliary diagram along two same-null routes.
The source route is the proved original Model equality cast. Cancellation uses
the actual empty-open Model-forget isomorphism, without assuming injectivity of
a general supported K-group forget map.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
attribute [local instance] basicOver_compactSpace basicOver_quasiSeparatedSpace
open GlobalSupportedSection GlobalSectionChangeIndex ParameterAuxiliarySupport
open ParameterLaurentTrack ParameterLaurentUnit
open ParameterAuxiliaryNormalizedRowLocalization

private theorem boundary_two_routes {C : Type*} [Category C]
    {A B D E F G H I : C}
    (δ : A ⟶ B) (δb : D ⟶ E) (δa : F ⟶ G) (δn : H ⟶ I)
    (p : A ⟶ D) [Epi p] (q : B ⟶ E) (v : B ⟶ G) (w : A ⟶ F)
    (r : F ⟶ H) (s : G ⟶ I) (x : D ⟶ H) (y : E ⟶ I)
    (hb : δ ≫ q = p ≫ δb) (ha : δ ≫ v = w ≫ δa)
    (hn : δa ≫ s = r ≫ δn) (hq : q ≫ y = v ≫ s) (hp : p ≫ x = w ≫ r) :
    δb ≫ y = x ≫ δn := by
  apply (cancel_epi p).1
  calc
    p ≫ (δb ≫ y) = (δ ≫ q) ≫ y := by rw [hb, Category.assoc]
    _ = (δ ≫ v) ≫ s := by rw [Category.assoc, hq, ← Category.assoc]
    _ = (w ≫ r) ≫ δn := by rw [ha, Category.assoc, hn, ← Category.assoc]
    _ = p ≫ (x ≫ δn) := by rw [← hp, Category.assoc]

private theorem map_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E G : C} (a : A ⟶ B) (b : B ⟶ G)
    (c : A ⟶ E) (d : E ⟶ G) (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

private theorem isIso_left_of_square {C : Type*} [Category C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ D) (d : D ⟶ E)
    [IsIso b] [IsIso c] [IsIso d] (h : a ≫ b = c ≫ d) : IsIso a := by
  have : IsIso (a ≫ b) := h.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right a b

private theorem mapped_open_forget_square {P Q : Scheme.{u}} (f : P ⟶ Q)
    (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).map ((currentOpenForget f T).app X) ≫
        (stableHomotopyFunctor d).map
          (ParameterTensorNormalizedRowPresentation.ambientComparison P X) =
      (stableHomotopyFunctor d).map
          (ParameterTensorNormalizedRowPresentation.supportedComparison (inverseOpen f T).ι X) ≫
        (stableHomotopyFunctor d).map
          (ParameterTensorNormalizedRowPresentation.forget (inverseOpen f T).ι X) :=
  map_square (stableHomotopyFunctor d) _ _ _ _
    (ParameterTensorNormalizedRowPresentation.current_forget_square (inverseOpen f T).ι X)

private theorem current_open_forget_isIso {P Q : Scheme.{u}} (f : P ⟶ Q)
    (T : Q.Opens) [IsEmpty (inverseOpen f T).toScheme]
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map ((currentOpenForget f T).app X)) := by
  have : IsIso ((stableHomotopyFunctor d).map
      (ParameterTensorNormalizedRowPresentation.ambientComparison P X)) :=
    ParameterTensorNormalizedRowPresentation.ambientComparison_stable P X d
  have : IsIso ((stableHomotopyFunctor d).map
      (ParameterTensorNormalizedRowPresentation.supportedComparison (inverseOpen f T).ι X)) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable (inverseOpen f T).ι X d
  have : IsIso ((stableHomotopyFunctor d).map
      (ParameterTensorNormalizedRowPresentation.forget (inverseOpen f T).ι X)) :=
    ParameterTensorNormalizedRowPresentation.forget_stable_of_isEmpty (inverseOpen f T).ι X d
  exact isIso_left_of_square _ _ _ _ (mapped_open_forget_square f T X d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem current_normalized_of_auxiliary
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]
    [IsEmpty (inverseOpen f.left T).toScheme]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ)
    (s : ParameterTensorNormalizedRowPresentation.supported (unionOpen f.left T).ι
        (specUnder.obj a) ⟶
      ParameterTensorNormalizedRowPresentation.supported f.left (specUnder.obj a))
    (δn : stableHomotopyGroup
        (ParameterTensorNormalizedRowPresentation.ambient P.left (specUnder.obj a)) (d + 1) ⟶
      stableHomotopyGroup
        (ParameterTensorNormalizedRowPresentation.supported f.left (specUnder.obj a)) d)
    (hs : (currentToBasic f.left T).app (specUnder.obj a) ≫
        ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a) =
      normalizedFiberPresentationComparison f.left T (specUnder.obj a) ≫ s)
    (hn : normalizedPresentationConnecting f T a d ≫ (stableHomotopyFunctor d).map s =
      (stableHomotopyFunctor (d + 1)).map
          (ParameterTensorNormalizedRowPresentation.forget (inverseOpen f.left T).ι
            (specUnder.obj a)) ≫ δn) :
    ParameterFullCurrentNull.currentConnecting f a d ≫
        (stableHomotopyFunctor d).map
          (ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a)) =
      (stableHomotopyFunctor (d + 1)).map
          (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a)) ≫
        δn := by
  have : IsIso ((stableHomotopyFunctor (d + 1)).map
      ((currentOpenForget f.left T).app (specUnder.obj a))) :=
    current_open_forget_isIso f.left T (specUnder.obj a) (d + 1)
  exact boundary_two_routes _ _ _ _ _ _ _ _ _ _ _ _
    (current_auxiliary_basic_connecting f T a d)
    (current_normalizedPresentation_connecting f T a d) hn
    (map_square (stableHomotopyFunctor d) _ _ _ _ hs)
    (mapped_open_forget_square f.left T (specUnder.obj a) (d + 1))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original full-open current boundary follows the actual normalized row comparisons. -/
theorem current_basic_normalized_connecting (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    ParameterFullCurrentNull.currentConnecting (basicOverInclusion Q U) a d ≫
      (stableHomotopyFunctor d).map
        (ParameterTensorNormalizedRowPresentation.supportedComparison U.ι (specUnder.obj a)) =
    (stableHomotopyFunctor (d + 1)).map
        (ParameterTensorNormalizedRowPresentation.ambientComparison U.toScheme (specUnder.obj a)) ≫
      basicSpecConnecting Q U a d := by
  have : IsEmpty (inverseOpen (basicOverInclusion Q U).left ⊥).toScheme := by
    change IsEmpty (inverseOpen U.ι (⊥ : Q.Opens)).toScheme
    rw [inverseOpen_bottom]
    infer_instance
  exact current_normalized_of_auxiliary (basicOverInclusion Q U) ⊥ a d
    (basicSourceIso Q U (specUnder.obj a)).hom (basicSpecConnecting Q U a d)
    (currentToBasic_sourceIso_square Q U (specUnder.obj a))
    (auxiliary_basic_spec_connecting Q U a d)

end AlgebraicGeometry.Scheme.Modules.ParameterNormalizedBasicLocalization
