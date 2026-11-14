/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.PresheafAdjunction
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.CategoryTheory.Prespectrum.SmallObject
public import Colib.CategoryTheory.Sites.Simplicial.BoundedMonoGenerators
public import Colib.CategoryTheory.Sites.Simplicial.BoundedTrivialLifting

/-!
# Projective level factorizations for strict Tate prespectra

The strict Tate suspension is the existing left adjoint. The generic
prespectrum small-object construction applies to the actual bounded
pointed-presheaf generating families, with the indicated right lifting
classes at every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf
open CategoryTheory.SequentialPrespectrum AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})
local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Sᵣ" => tatePresheafSuspension R

/-- Any small family of pointed smooth-site maps gives a functorial level
factorization for the strict Tate suspension. -/
theorem tateLevel_hasFunctorialFactorization
    {ι : Type (u + 1)} {A B : ι → PointedSimplicialPresheaf.{u + 1} Cᵣ}
    (i : ∀ a, A a ⟶ B a) :
    MorphismProperty.HasFunctorialFactorization
      (levelwise (S := Sᵣ) (MorphismProperty.ofHoms i).rlp).llp
      (levelwise (S := Sᵣ) (MorphismProperty.ofHoms i).rlp) := by
  let : Functor.IsLeftAdjoint (tatePresheafSuspension R) :=
    (tatePresheafAdjunction R).isLeftAdjoint
  let : LocallySmall.{u + 1} (PointedSimplicialPresheaf.{u + 1} Cᵣ) := locallySmall_self _
  exact levelwise_hasFunctorialFactorization_of_domains_presentable i
    (fun _ ↦ isPresentable_pointedSimplicialPresheaf _)

/-- The bounded mono generators give the projective level factorization. -/
theorem tateLevelBoundedMono_hasFunctorialFactorization (κ : Cardinal.{u + 1}) :
    MorphismProperty.HasFunctorialFactorization
      (levelwise (S := Sᵣ) (boundedMonoGenerators Cᵣ κ).rlp).llp
      (levelwise (S := Sᵣ) (boundedMonoGenerators Cᵣ κ).rlp) := by
  exact tateLevel_hasFunctorialFactorization R
    (fun q : BoundedMonoArrow Cᵣ κ ↦ (free Cᵣ).map q.val.2.2)

/-- Under the original cardinal bound, the right factor lifts levelwise
against every pointed-presheaf monomorphism. -/
theorem tateLevelMono_hasFunctorialFactorization (κ : Cardinal.{u + 1})
    (hC : ∀ q : Cᵣᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵣᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ) :
    MorphismProperty.HasFunctorialFactorization
      (levelwise (S := Sᵣ) (MorphismProperty.monomorphisms _).rlp).llp
      (levelwise (S := Sᵣ) (MorphismProperty.monomorphisms _).rlp) := by
  rw [← rlp_boundedMonoGenerators_eq Cᵣ κ hC]
  exact tateLevelBoundedMono_hasFunctorialFactorization R κ

/-- The bounded stalkwise trivial generators give a second projective level
factorization on the same strict Tate prespectra. -/
theorem tateLevelBoundedTrivial_hasFunctorialFactorization (κ : Cardinal.{u + 1}) :
    MorphismProperty.HasFunctorialFactorization
      (levelwise (S := Sᵣ) (boundedTrivialGenerators Cᵣ Jᵣ κ).rlp).llp
      (levelwise (S := Sᵣ) (boundedTrivialGenerators Cᵣ Jᵣ κ).rlp) := by
  exact tateLevel_hasFunctorialFactorization R
    (fun q : BoundedTrivialArrow Cᵣ Jᵣ κ ↦ (free Cᵣ).map q.val.2.2)

/-- Under the existing conservative-point and cardinal bounds, the right
factor lifts levelwise against all stalkwise trivial monomorphisms. -/
theorem tateLevelStalkwiseFibration_hasFunctorialFactorization
    {F : ObjectProperty (GrothendieckTopology.Point.{u + 1} Jᵣ)} [ObjectProperty.Small.{u + 1} F]
    (hF : F.IsConservativeFamilyOfPoints) (κ : Cardinal.{u + 1})
    [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hFκ : HasCardinalLT F.FullSubcategory κ)
    (hC : ∀ q : Cᵣᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵣᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ)
    (hPoint : ∀ ψ : F.FullSubcategory, ∀ U : Cᵣ,
      HasCardinalLT (ψ.obj.fiber.obj U) κ) :
    MorphismProperty.HasFunctorialFactorization
      (levelwise (S := Sᵣ) (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp).llp
      (levelwise (S := Sᵣ) (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp) := by
  rw [← rlp_boundedTrivialGenerators_eq Cᵣ Jᵣ hF κ hκ hFκ hC hPoint]
  exact tateLevelBoundedTrivial_hasFunctorialFactorization R κ

end AlgebraicGeometry.MotivicHomotopy
