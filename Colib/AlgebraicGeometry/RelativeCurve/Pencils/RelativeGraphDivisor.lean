/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Picard.DiagonalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme

/-!
# The actual graph divisor on the retained relative curve

For `D = X ×[S] V` and an actual map `φ : X ⟶ V` over `S`, its graph is a section
of `D ⟶ X`. If `V ⟶ S` is a separated smooth relative curve, the pinned native
section theorem makes its actual kernel ideal an effective Cartier divisor. The
whole closed graph scheme is isomorphic to the unchanged source, with both source
and target maps preserved. Its native canonical section has exactly this zero ideal.

This is the retained diagonal used by
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Data/Core.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
No ground field, integral source, reduced source, or absolute curve hypothesis is added.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X V : Scheme.{u}} (q : X ⟶ S) (r : V ⟶ S)
  (φ : X ⟶ V) (hφ : φ ≫ r = q)

/-- The literal graph of the retained target map, with the original source coordinate. -/
def relativeGraph : X ⟶ pullback q r :=
  pullback.lift (𝟙 X) φ (by simpa using hφ.symm)

@[reassoc (attr := simp)]
theorem relativeGraph_fst : relativeGraph q r φ hφ ≫ pullback.fst q r = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relativeGraph_snd : relativeGraph q r φ hφ ≫ pullback.snd q r = φ :=
  pullback.lift_snd _ _ _

instance [IsSeparated r] : IsClosedImmersion (relativeGraph q r φ hφ) := by
  have : IsClosedImmersion (relativeGraph q r φ hφ ≫ pullback.fst q r) := by
    rw [relativeGraph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (relativeGraph q r φ hφ) (pullback.fst q r)

/-- The genuine scheme-theoretic graph ideal, not its radical. -/
def relativeGraphIdeal : (pullback q r).IdealSheafData := (relativeGraph q r φ hφ).ker

instance [IsSeparated r] [SmoothOfRelativeDimension 1 r] :
    IsEffectiveCartierDivisor (relativeGraphIdeal q r φ hφ) := by
  have : SmoothOfRelativeDimension 1 (pullback.fst q r) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback q r).flip inferInstance
  exact Stacks.Hilbert.isEffectiveCartierDivisor_ker_section
    (f := pullback.fst q r) (relativeGraph q r φ hφ) (relativeGraph_fst q r φ hφ)

instance [IsSeparated r] : IsIso (relativeGraph q r φ hφ).toImage := by
  let g := relativeGraph q r φ hφ
  exact IsClosedImmersion.isIso_of_ker_eq g g.imageι g.toImage g.toImage_imageι
    (Scheme.IdealSheafData.ker_subschemeι g.ker).symm

/-- The closed graph's entire image scheme is the original source scheme. -/
def relativeGraphSupportIso [IsSeparated r] :
    (relativeGraphIdeal q r φ hφ).subscheme ≅ X :=
  (asIso (relativeGraph q r φ hφ).toImage).symm

@[reassoc (attr := simp)]
theorem relativeGraphSupportIso_hom_graph [IsSeparated r] :
    (relativeGraphSupportIso q r φ hφ).hom ≫ relativeGraph q r φ hφ =
      (relativeGraphIdeal q r φ hφ).subschemeι := by
  change inv (relativeGraph q r φ hφ).toImage ≫ relativeGraph q r φ hφ =
    (relativeGraph q r φ hφ).imageι
  exact (IsIso.inv_comp_eq (relativeGraph q r φ hφ).toImage).2
    (relativeGraph q r φ hφ).toImage_imageι.symm

@[reassoc]
theorem relativeGraphSupportIso_hom_base [IsSeparated r] :
    (relativeGraphSupportIso q r φ hφ).hom =
      (relativeGraphIdeal q r φ hφ).subschemeι ≫ pullback.fst q r := by
  rw [← relativeGraphSupportIso_hom_graph, Category.assoc, relativeGraph_fst,
    Category.comp_id]

@[reassoc]
theorem relativeGraphSupportIso_hom_target [IsSeparated r] :
    (relativeGraphSupportIso q r φ hφ).hom ≫ φ =
      (relativeGraphIdeal q r φ hφ).subschemeι ≫ pullback.snd q r := by
  rw [← relativeGraphSupportIso_hom_graph, Category.assoc, relativeGraph_snd]

/-- The whole graph divisor is flat over the unchanged source, because that projection
is its actual support isomorphism. -/
theorem relativeCartier_relativeGraphIdeal [IsSeparated r] [SmoothOfRelativeDimension 1 r] :
    IsRelativeEffectiveCartierDivisor (pullback.fst q r) (relativeGraphIdeal q r φ hφ) := by
  refine ⟨inferInstance, ?_⟩
  rw [← relativeGraphSupportIso_hom_base]
  infer_instance

/-- The native section of the graph line cuts out the original full graph ideal. -/
theorem zeroScheme_relativeGraphCanonicalSection [IsSeparated r]
    [SmoothOfRelativeDimension 1 r] :
    zeroScheme (pullback q r) (divisorSheaf (relativeGraphIdeal q r φ hφ))
      (divisorSheafGlobalSection (relativeGraphIdeal q r φ hφ)) = relativeGraphIdeal q r φ hφ :=
  zeroScheme_canonicalSection _

end AlgebraicGeometry.Scheme.RelativeCurvePencil
