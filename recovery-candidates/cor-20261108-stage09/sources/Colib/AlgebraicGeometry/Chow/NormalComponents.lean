/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Connected.Clopen

/-!
# Actual components of a normal locally Noetherian scheme

The native normal decomposition implies that irreducible components are clopen and
pairwise disjoint. Their actual reduced closed subscheme inclusions are open immersions.
The source may be empty or disconnected; no chosen decomposition replaces the native
`integralComponentAt` construction.

Mathematical references: Stacks Project, Tag 0357 (Lemma 28.7.5), especially the
open-and-closed irreducible component consequence; Tag 033N (Lemma 28.7.7) is the
locally Noetherian specialization. The proof consumes the pinned native theorem
`isNormal_iff_exists_iso_coproduct` rather than reproving normal decomposition.

Recovery status: fresh reconstruction from retained declaration/proof descriptions,
not the lost historical source bytes; not compiled in this recovery task.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An actual irreducible component of a normal locally Noetherian scheme is clopen. -/
@[stacks 0357 "open-and-closed irreducible component consequence"]
theorem isClopen_of_mem_irreducibleComponents_of_isNormal
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (C : Set X) (hC : C ∈ irreducibleComponents X) : IsClopen C := by
  classical
  obtain ⟨ι, Y, _, hY, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct
      (finite_irreducibleComponents_of_isCompact X)).mp ‹IsNormal X›
  let : ∀ i, IsIntegral (Y i) := hY
  let E : X ≃ₜ (Σ i, Y i) := (Scheme.homeoOfIso e).trans (sigmaMk Y).symm
  obtain ⟨x, hx⟩ := hC.1.nonempty
  let i := (E x).1
  let V : Set X := E.symm '' Set.range (Sigma.mk i)
  have hV : IsClopen V :=
    ⟨E.symm.isClosedMap _ isClopen_range_sigmaMk.isClosed,
      E.symm.isOpenMap _ isClopen_range_sigmaMk.isOpen⟩
  have hxV : x ∈ V := ⟨E x, ⟨(E x).2, rfl⟩, E.symm_apply_apply x⟩
  have hCV : C ⊆ V := hC.1.2.isPreconnected.subset_isClopen hV ⟨x, hx, hxV⟩
  have hVirr : IsIrreducible V := by
    have hR : IsIrreducible (Set.range (Sigma.mk i) : Set (Σ j, Y j)) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ (Y i)).image _
        continuous_sigmaMk.continuousOn
    exact hR.image E.symm E.symm.continuous.continuousOn
  have hEq : C = V := Set.Subset.antisymm hCV (hC.2 hVirr hCV)
  rw [hEq]
  exact hV

/-- Distinct actual irreducible components of a normal locally Noetherian scheme are disjoint. -/
@[stacks 0357 "pairwise disjoint irreducible component consequence"]
theorem disjoint_of_mem_irreducibleComponents_of_isNormal
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (C D : Set X) (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) (hne : C ≠ D) : Disjoint C D := by
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  have hCD : C ⊆ D := hC.1.2.isPreconnected.subset_isClopen
    (isClopen_of_mem_irreducibleComponents_of_isNormal D hD) ⟨x, hxC, hxD⟩
  exact hne (Set.Subset.antisymm hCD (hC.2 hD.1 hCD))

end AlgebraicGeometry

namespace Stacks.Chow

/-- The native integral component inclusion at a generic point is an open immersion. -/
theorem isOpenImmersion_integralComponentAt_of_isNormal
    {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (t : genericPoints X) :
    IsOpenImmersion (integralComponentAt t.val).subschemeι := by
  let U : X.Opens := ⟨closure {t.val},
    (isClopen_of_mem_irreducibleComponents_of_isNormal _ t.property).isOpen⟩
  have hrange : Set.range (integralComponentAt t.val).subschemeι = Set.range U.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt,
      Scheme.Opens.range_ι]
    rfl
  let l := IsOpenImmersion.lift U.ι (integralComponentAt t.val).subschemeι hrange.le
  have hl : l ≫ U.ι = (integralComponentAt t.val).subschemeι :=
    IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (l ≫ U.ι) := by rw [hl]; infer_instance
  let : IsClosedImmersion l := IsClosedImmersion.of_comp l U.ι
  let : Surjective l := ⟨by
    intro y
    obtain ⟨x, hx⟩ := hrange.symm ▸ (show U.ι y ∈ Set.range U.ι from ⟨y, rfl⟩)
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, hl] using hx⟩
  let : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  rw [← hl]
  infer_instance

end Stacks.Chow
