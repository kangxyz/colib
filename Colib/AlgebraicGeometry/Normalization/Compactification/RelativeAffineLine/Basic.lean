/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.Etale
public import Colib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.NativeLine
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# The actual relative normalization of an étale affine-line source

Compose the original étale morphism with the native polynomial chart and
take its relative normalization. Over a normal finite type coefficient
domain over a field, the resulting projective-line morphism is finite.
The open inclusion and the whole missing boundary retain their original
maps to the compactification.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
`Normalization/Compactification/RelativeAffineLine/Basic.lean` and
`Normalization/Compactification/Boundary/InfinityBoundary.lean`
under `Motivic/Aglib/AlgebraicGeometry`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.RelativeCurve

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R)))

/-- The original étale map in the chosen native projective line. -/
abbrev projectiveMap : Y ⟶ projectiveSpaceOverRing 1 (.of R) :=
  p ≫ NativeProjectiveLine.chart R

variable [IsNoetherianRing R] [Etale p] [QuasiCompact p] [IsSeparated p]

instance projectiveMap_quasiCompact : QuasiCompact (projectiveMap R p) := by
  let : QuasiCompact (NativeProjectiveLine.chart R) := quasiCompact_of_noetherianSpace_source _
  change QuasiCompact (p ≫ NativeProjectiveLine.chart R)
  infer_instance

/-- Relative normalization of the original source over the native projective line. -/
abbrev compactification : Scheme.{u} := (projectiveMap R p).normalization

/-- The canonical inclusion of the original étale source. -/
abbrev inclusion : Y ⟶ compactification R p := (projectiveMap R p).toNormalization

/-- The actual structural morphism of the normalization. -/
abbrev toProjectiveLine : compactification R p ⟶ projectiveSpaceOverRing 1 (.of R) :=
  (projectiveMap R p).fromNormalization

/-- The original coefficient-base projection of the compactification. -/
abbrev projection : compactification R p ⟶ Spec (.of R) :=
  toProjectiveLine R p ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))

omit [IsSeparated p] in
@[reassoc (attr := simp)]
theorem inclusion_toProjectiveLine :
    inclusion R p ≫ toProjectiveLine R p = p ≫ NativeProjectiveLine.chart R :=
  (projectiveMap R p).toNormalization_fromNormalization

omit [IsSeparated p] in
@[reassoc (attr := simp)]
theorem inclusion_projection :
    inclusion R p ≫ projection R p = p ≫ polynomialProjection (.of R) := by
  rw [projection, ← Category.assoc, inclusion_toProjectiveLine, Category.assoc,
    NativeProjectiveLine.chart_projection, polynomialProjection]

instance inclusion_open : IsOpenImmersion (inclusion R p) :=
  EtaleCompactification.open_normalization (projectiveMap R p)

/-- Finiteness of the relative normalization over the original finite type
normal coefficient domain. -/
theorem toProjectiveLine_finite (k : Type u) [Field k] [Algebra k R]
    [Algebra.FiniteType k R] [IsDomain R] [IsIntegrallyClosed R] :
    IsFinite (toProjectiveLine R p) := by
  let b := (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
  let a := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have : LocallyOfFiniteType a := (HasRingHomProperty.Spec_iff
    (P := @LocallyOfFiniteType)).mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have : IsNormal (Spec (.of R)) := isNormal_spec_of_isIntegrallyClosed R
  have : IsNormal (projectiveSpaceOverRing 1 (.of R)) := isNormal_of_smooth b
  exact EtaleCompactification.finite_normalization k (b ≫ a) (projectiveMap R p)

/-- The reduced closed complement of the entire original open inclusion. -/
def infinityIdeal : (compactification R p).IdealSheafData :=
  IdealSheafData.vanishingIdeal
    ⟨(Set.range (inclusion R p))ᶜ,
      (inclusion R p).isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- The whole closed boundary of the original open. -/
abbrev infinity : Scheme.{u} := (infinityIdeal R p).subscheme

/-- The original closed inclusion of the entire boundary. -/
abbrev infinityInclusion : infinity R p ⟶ compactification R p :=
  (infinityIdeal R p).subschemeι

instance infinityInclusion_closed : IsClosedImmersion (infinityInclusion R p) :=
  inferInstanceAs (IsClosedImmersion (infinityIdeal R p).subschemeι)

/-- The original closed boundary covers the entire complement of the source. -/
theorem range_infinityInclusion :
    Set.range (infinityInclusion R p) = (Set.range (inclusion R p))ᶜ := by
  rw [infinityInclusion, IdealSheafData.range_subschemeι]
  simp [infinityIdeal]

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
