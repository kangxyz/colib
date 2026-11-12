/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Topology
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Topology
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Étale cover transport between the separated finite-type and smooth sites

For an affine base `B` and an arbitrary `X : SmoothSite B`, the existing
`toSmoothSite X` is continuous and cocontinuous for the actual étale topologies.
Both statements retain the original scheme maps. The topology on the small
basis is the topology induced from the full small étale site, not a new
precoverage. The smooth object `X` need not be affine.

Continuity uses actual covering-sieve transport and the existing pullback
preservation. Cocontinuity lifts a smooth étale covering family to separated,
quasi-compact étale neighborhoods of `X`. No sheaf-extension exactness or
derived cohomology comparison is asserted.

Adapted from the corresponding Motivic source checkpoint of 2026-10-21.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- The inclusion retains the actual pullbacks of neighborhoods. -/
instance toSmoothSite_preservesPullbacks {B : Scheme.{u}} (X : SmoothSite B) :
    PreservesLimitsOfShape WalkingCospan (toSmoothSite X) := by
  have : PreservesLimitsOfShape WalkingCospan
      (toSmoothSite X ⋙ SmoothSite.forgetScheme B) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (forgetScheme X.left))
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (toSmoothSite X) (SmoothSite.forgetScheme B)

variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)

/-- A family in the actual small basis is étale covering exactly when it is jointly surjective. -/
theorem ofArrows_mem_etaleTopology_iff {U : EtaleSeparatedFiniteType X.left} {ι : Type*}
    {V : ι → EtaleSeparatedFiniteType X.left} (f : ∀ i, V i ⟶ U) :
    Sieve.ofArrows V f ∈ etaleTopology X.left U ↔
      ∀ x : U.left, ∃ (i : ι) (y : (V i).left), (f i).left y = x := by
  let := toSmallEtale_isCoverDense X
  change Sieve.ofArrows V f ∈
    (toSmallEtale X.left).inducedTopology X.left.smallEtaleTopology U ↔ _
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    Sieve.functorPushforward_ofArrows, Scheme.ofArrows_mem_smallEtaleTopology_iff]
  simp only [toSmallEtale_map_left, toSmallEtale_obj_left,
    Set.iUnion_eq_univ_iff, Set.mem_range]
  rfl

/-- The existing functor sends covering sieves to covering sieves without changing scheme maps. -/
theorem toSmoothSite_etale_coverPreserving :
    CoverPreserving (etaleTopology X.left) (SmoothSite.etaleTopology B)
      (toSmoothSite X) where
  cover_preserve {U} {R} hR := by
    obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows]
    apply Precoverage.generate_mem_toGrothendieck
    apply (SmoothSite.ofArrows_mem_etalePrecoverage_iff _).mpr
    refine ⟨fun i ↦ ?_, (ofArrows_mem_etaleTopology_iff X f).mp hR⟩
    change Etale (f i).left
    have : Etale ((f i).left ≫ U.hom) := by
      rw [MorphismProperty.Over.w]
      infer_instance
    exact Etale.of_comp (f i).left U.hom

/-- Literal restriction along `toSmoothSite X` sends smooth étale sheaves to basis sheaves. -/
instance toSmoothSite_etale_isContinuous :
    (toSmoothSite X).IsContinuous (etaleTopology X.left) (SmoothSite.etaleTopology B) := by
  let : (toSmoothSite X).PreservesOneHypercovers.{u + 1}
      (etaleTopology X.left) (SmoothSite.etaleTopology B) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (toSmoothSite_etale_coverPreserving X)
  infer_instance

/-- A smooth étale cover of a basis object contains a covering family over the original `X`. -/
theorem exists_toSmoothSite_etale_cover_lift {U : EtaleSeparatedFiniteType X.left}
    {R : Sieve ((toSmoothSite X).obj U)}
    (hR : R ∈ SmoothSite.etaleTopology B _) :
    ∃ Q ∈ etaleTopology X.left U, Q ≤ R.functorPullback (toSmoothSite X) := by
  obtain ⟨R₀, hR₀, h₀⟩ := SmoothSite.mem_etaleTopology_iff.mp hR
  obtain ⟨ι, V, f, rfl⟩ := R₀.exists_eq_ofArrows
  have hf := (SmoothSite.ofArrows_mem_etalePrecoverage_iff f).mp hR₀
  let a (i : ι) : (V i).left ⟶ U.left := (f i).left
  let (i : ι) : Etale (a i) := hf.1 i
  have hw (i : ι) : (a i ≫ U.hom) ≫ X.hom = (V i).hom := by
    exact (Category.assoc (a i) U.hom X.hom).trans (f i).w
  let (i : ι) : IsSeparated (a i ≫ U.hom) := by
    have : IsSeparated ((a i ≫ U.hom) ≫ X.hom) := by
      rw [hw i]
      infer_instance
    exact IsSeparated.of_comp _ X.hom
  let (i : ι) : QuasiCompact (a i ≫ U.hom) := by
    have : QuasiCompact ((a i ≫ U.hom) ≫ X.hom) := by
      rw [hw i]
      infer_instance
    exact QuasiCompact.of_comp _ X.hom
  let W (i : ι) : EtaleSeparatedFiniteType X.left :=
    MorphismProperty.Over.mk ⊤ (a i ≫ U.hom)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let g (i : ι) : W i ⟶ U := MorphismProperty.Over.homMk (a i) rfl
  refine ⟨Sieve.ofArrows W g, (ofArrows_mem_etaleTopology_iff X g).mpr hf.2, ?_⟩
  change Sieve.generate (Presieve.ofArrows W g) ≤ _
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  let e : (toSmoothSite X).obj (W i) ⟶ V i :=
    SmoothSite.homMk (𝟙 _) (by
      change 𝟙 _ ≫ (V i).hom = (a i ≫ U.hom) ≫ X.hom
      simpa only [Category.id_comp] using (hw i).symm)
  have he : e ≫ f i = (toSmoothSite X).map (g i) := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 _ ≫ a i = a i
    exact Category.id_comp _
  change R ((toSmoothSite X).map (g i))
  rw [← he]
  exact R.downward_closed (h₀ _ _ ⟨i⟩) e

/-- Smooth étale covering sieves pull back to covering sieves on the actual small basis. -/
instance toSmoothSite_etale_isCocontinuous :
    (toSmoothSite X).IsCocontinuous (etaleTopology X.left) (SmoothSite.etaleTopology B) where
  cover_lift hR := by
    obtain ⟨Q, hQ, hQR⟩ := exists_toSmoothSite_etale_cover_lift X hR
    exact (etaleTopology X.left).superset_covering hQR hQ

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
