/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Affine refinement of Nisnevich covers of smooth schemes

Over an affine base, every big Nisnevich covering sieve at a smooth-site object
contains the image of a small Nisnevich covering family. The members of a big
cover need not be separated or quasi-compact: first refine each of them by its
affine open cover. Their composites to the base are smooth, separated and
quasi-compact, so these refined sources are actual smooth-site objects.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Nisnevich/Refinement.lean`
at `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
Mathlib supplies the restricted and induced topology and the general cocontinuity API.
The only new geometric input is the affine-open refinement into the existing smooth site.

This is a statement about covering sieves. Restricting a raw big covering
presieve to smooth-site sources need not remain a covering presieve.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [IsAffine S]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every big Nisnevich covering sieve of a smooth-site object contains a
small Nisnevich covering family. The proof refines every source by affine opens. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Nisnevich/Refinement.lean:39-61"
  "adaptation" "Affine-open refinement of big Nisnevich covering sieves at smooth objects \
    over an affine base, without separatedness or quasi-compactness of big cover sources"]
theorem exists_nisnevich_refinement (X : SmoothSite S) {R : Sieve X.left}
    (hR : R ∈ Nisnevich.topology X.left) :
    ∃ Q : Presieve X, Q ∈ nisnevichPrecoverage S X ∧
      Q ≤ (R.functorPullback (forgetScheme S)).arrows := by
  obtain ⟨R₀, hR₀, h₀⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨ι, Y, f, rfl⟩ := R₀.exists_eq_ofArrows
  let (i : ι) : Etale (f i) :=
    ((Nisnevich.ofArrows_mem_precoverage_iff f).mp hR₀).1 i
  let Z (p : Σ i, (Y i).affineCover.I₀) : SmoothSite S :=
    mk ((Y p.1).affineCover.f p.2 ≫ f p.1 ≫ X.hom)
  let g (p : Σ i, (Y i).affineCover.I₀) : Z p ⟶ X :=
    homMk ((Y p.1).affineCover.f p.2 ≫ f p.1) (by simp [Z])
  refine ⟨Presieve.ofArrows Z g, ?_, ?_⟩
  · change (Presieve.ofArrows Z g).map (forgetScheme S) ∈
      Nisnevich.precoverage X.left
    rw [Presieve.map_ofArrows]
    exact Precoverage.comp_mem_coverings f hR₀
      (fun i j ↦ (Y i).affineCover.f j)
      (fun i ↦ Nisnevich.zariskiPrecoverage_le_precoverage _ (Y i).affineCover.mem₀)
  · rw [Presieve.ofArrows_le_iff]
    intro p
    exact R.downward_closed (h₀ _ _ ⟨p.1⟩) ((Y p.1).affineCover.f p.2)

set_option backward.isDefEq.respectTransparency false in
/-- The refinement statement in the category of schemes over the base. -/
theorem exists_nisnevich_refinement_over (X : SmoothSite S)
    {R : Sieve ((forget S).obj X)} (hR : R ∈ (Nisnevich.topology.over S) _) :
    ∃ Q : Presieve X, Q ∈ nisnevichPrecoverage S X ∧
      Q ≤ (R.functorPullback (forget S)).arrows := by
  obtain ⟨Q, hQ, hQR⟩ := exists_nisnevich_refinement X
    ((Nisnevich.topology.mem_over_iff R).mp hR)
  refine ⟨Q, hQ, ?_⟩
  change Q ≤ ((R.functorPushforward (Over.forget S)).functorPullback
    (forget S ⋙ Over.forget S)).arrows at hQR
  rw [Sieve.functorPullback_comp,
    Sieve.functorPullback_functorPushforward_overForget] at hQR
  exact hQR

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of smooth-site objects is locally cover dense for the big
Nisnevich topology. This does not assert that every scheme is covered by smooth schemes. -/
instance forget_locallyCoverDense_nisnevich :
    (forget S).LocallyCoverDense (Nisnevich.topology.over S) where
  functorPushforward_functorPullback_mem {X} T := by
    obtain ⟨Q, hQ, hQT⟩ := exists_nisnevich_refinement_over X T.property
    apply (Nisnevich.topology.over S).superset_covering
      (S := (Sieve.generate Q).functorPushforward (forget S))
    · exact Sieve.functorPushforward_monotone _ _ ((Sieve.generate_le_iff _ _).mpr hQT)
    · change ((Sieve.generate Q).functorPushforward (forget S)).functorPushforward
        (Over.forget S) ∈ Nisnevich.topology X.left
      rw [← Sieve.functorPushforward_comp, ← Sieve.generate_map_eq_functorPushforward]
      exact Precoverage.generate_mem_toGrothendieck hQ

/-- Over an affine base, the family-generated small Nisnevich topology agrees
with the restriction of the big Nisnevich topology on schemes over the base. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Nisnevich/Refinement.lean:95-109"
  "adaptation" "For an affine base, the existing family-generated smooth Nisnevich topology \
    equals the native restricted topology on schemes over the base"]
theorem nisnevichTopology_eq_restrictedTopology (S : Scheme.{u}) [IsAffine S] :
    nisnevichTopology S = (forget S).restrictedTopology (Nisnevich.topology.over S) := by
  refine le_antisymm ?_ ?_
  · change (Nisnevich.precoverage.comap (forget S ⋙ Over.forget S)).toGrothendieck ≤ _
    rw [Precoverage.comap_comp]
    simpa only [Nisnevich.topology,
      over_toGrothendieck_eq_toGrothendieck_comap_forget] using
      (Precoverage.toGrothendieck_comap_le_restrictedTopology
        (F := forget S) (Nisnevich.precoverage.comap (Over.forget S)))
  · intro X R hR
    rw [Functor.mem_restrictedTopology_iff] at hR
    obtain ⟨Q, hQ, hQR⟩ := exists_nisnevich_refinement_over X hR
    rw [Sieve.functorPullback_functorPushforward_eq] at hQR
    exact (nisnevichTopology S).superset_covering ((Sieve.generate_le_iff _ _).mpr hQR)
      (Precoverage.generate_mem_toGrothendieck hQ)

/-- A small sieve is Nisnevich covering exactly when its image generates a
covering sieve in the big site over the base. -/
theorem mem_nisnevichTopology_iff_functorPushforward {X : SmoothSite S} (R : Sieve X) :
    R ∈ nisnevichTopology S X ↔
      R.functorPushforward (forget S) ∈ (Nisnevich.topology.over S) ((forget S).obj X) := by
  rw [nisnevichTopology_eq_restrictedTopology, Functor.mem_restrictedTopology_iff]

/-- Over an affine base, the small Nisnevich topology also agrees with the
finest topology making the inclusion into the big over-site continuous. -/
theorem nisnevichTopology_eq_inducedTopology (S : Scheme.{u}) [IsAffine S] :
    nisnevichTopology S = (forget S).inducedTopology (Nisnevich.topology.over S) := by
  exact (Functor.restrictedTopology_eq_inducedTopology_of_isContinuous
    (nisnevichTopology_eq_restrictedTopology S).symm).symm

/-- Big Nisnevich covering sieves restrict to small covering sieves. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Nisnevich/Refinement.lean:126-129"
  "adaptation" "Cocontinuity of the existing smooth-site inclusion over an affine base"]
instance forget_isCocontinuous_nisnevich :
    (forget S).IsCocontinuous (nisnevichTopology S) (Nisnevich.topology.over S) := by
  rw [nisnevichTopology_eq_restrictedTopology]
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite

attribute [colib_tag "COL-0393"]
  AlgebraicGeometry.Scheme.SmoothSite.exists_nisnevich_refinement
  AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology_eq_restrictedTopology
  AlgebraicGeometry.Scheme.SmoothSite.mem_nisnevichTopology_iff_functorPushforward
  AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology_eq_inducedTopology
  AlgebraicGeometry.Scheme.SmoothSite.forget_isCocontinuous_nisnevich
  CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility
  CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Sites/CoverLifting.lean:367-371"
  "specialization" "Direct native reuse for ordinary sheafification \
    after affine Nisnevich restriction"]
  CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Sites/CoverLifting.lean:376-397"
  "specialization" "The actual sheafification comparison preserves \
    the restricted sheafification unit"]
  CategoryTheory.Functor.toSheafify_pullbackSheafificationCompatibility
