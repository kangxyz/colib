/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.LevelFactorization
public import Colib.CategoryTheory.Prespectrum.LevelCofibrations
public import Colib.CategoryTheory.Prespectrum.Limits
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Colib.CategoryTheory.Sites.Simplicial.MonoFactorization
import Colib.CategoryTheory.Sites.Simplicial.SmashMonomorphism
import Colib.CategoryTheory.Sites.Simplicial.BoundedIntersection
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialCoproduct
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialComposition
public import Colib.CategoryTheory.Sites.Simplicial.TrivialFibration
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.EnoughPoints

/-!
# Projective level classes on strict Tate prespectra

The weak equivalences and fibrations are defined levelwise using the
original Nisnevich stalkwise classes. Projective cofibrations lift against
the levelwise maps that lift against all pointed monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.PointedSimplicialPresheaf CategoryTheory.SequentialPrespectrum
open AlgebraicGeometry.Scheme Opposite

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})
local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Sᵣ" => tatePresheafSuspension R
local notation "Tᵣ" => SequentialPrespectrum Sᵣ

/-- Levelwise Nisnevich stalkwise weak equivalences. -/
def tateLevelWeakEquivalences : MorphismProperty Tᵣ :=
  levelwise (stalkwiseWeakEquivalences Cᵣ Jᵣ)

/-- Maps whose levels lift against stalkwise trivial monomorphisms. -/
def tateLevelFibrations : MorphismProperty Tᵣ :=
  levelwise (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp

/-- The projective left class of the levelwise trivial fibrations. -/
def tateProjectiveCofibrations : MorphismProperty Tᵣ :=
  (levelwise (S := Sᵣ) (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp).llp

/-- Projective Tate cofibrations are monomorphisms at each level. -/
theorem tateProjectiveCofibrations_le_levelwiseMono :
    tateProjectiveCofibrations R ≤
      levelwise (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)) := by
  let : Functor.IsLeftAdjoint Sᵣ := (tatePresheafAdjunction R).isLeftAdjoint
  let : LocallySmall.{u + 1} (PointedSimplicialPresheaf.{u + 1} Cᵣ) := locallySmall_self _
  let W := monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)
  let : W.IsStableUnderTransfiniteComposition.{u + 1} := ⟨fun _ ↦ inferInstance⟩
  let T := Σ q : Cᵣᵒᵖ × SimplexCategoryᵒᵖ, Σ r : Cᵣᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r
  obtain ⟨κ, _, hT⟩ := HasCardinalLT.exists_regular_cardinal.{u + 1} T
  have hC (q : Cᵣᵒᵖ × SimplexCategoryᵒᵖ) :
      HasCardinalLT (Σ r : Cᵣᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ :=
    hT.of_injective (fun s ↦ (⟨q, s⟩ : T))
      (by intro _ _ e; exact eq_of_heq (Sigma.mk.inj_iff.1 e).2)
  let i (q : BoundedMonoArrow Cᵣ κ) := (free Cᵣ).map q.val.2.2
  have hi (q : BoundedMonoArrow Cᵣ κ) :
      (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)) (i q) :=
    boundedMonoGenerators_le Cᵣ κ _ ⟨q⟩
  have hS : ∀ ⦃A B : (PointedSimplicialPresheaf.{u + 1} Cᵣ)⦄ (f : A ⟶ B),
      (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)) f →
        (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ))
          ((tatePresheafSuspension R).map f) := by
    intro A B f hf
    let : Mono f := hf
    exact mono_smashRightFunctor_map (liftedTateSphere R) f
  have h := projectiveLeft_le_levelwise_of_presentable (S := Sᵣ)
    (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)) hS i hi
    (fun _ ↦ isPresentable_pointedSimplicialPresheaf _)
  change (levelwise (S := Sᵣ) (boundedMonoGenerators Cᵣ κ).rlp).llp ≤
    levelwise (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)) at h
  rw [rlp_boundedMonoGenerators_eq Cᵣ κ hC] at h
  exact h

/-- The projective left class of the levelwise stalkwise fibrations. -/
def tateProjectiveTrivialCofibrations : MorphismProperty Tᵣ :=
  (tateLevelFibrations R).llp

/-- Projective trivial cofibrations are stalkwise trivial monomorphisms
in every degree. -/
theorem tateProjectiveTrivialCofibrations_le_levelwiseTrivialMono :
    tateProjectiveTrivialCofibrations R ≤ levelwise (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ) := by
  let : Functor.IsLeftAdjoint Sᵣ := (tatePresheafAdjunction R).isLeftAdjoint
  let : LocallySmall.{u + 1} (PointedSimplicialPresheaf.{u + 1} Cᵣ) := locallySmall_self _
  let : LocallySmall.{u + 1} Cᵣ := by infer_instance
  let W := stalkwiseTrivialMonomorphisms.{u + 1} Cᵣ Jᵣ
  let : W.IsStableUnderTransfiniteComposition.{u + 1} := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨F, hSmall, hF⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty Jᵣ
  let : ObjectProperty.Small.{u + 1} F := hSmall
  obtain ⟨κ, hReg, hκ, hFκ, hC, hPoint⟩ :=
    CategoryTheory.SimplicialSubpresheaf.exists_regular_cardinal_bounds (F := F)
  let : Fact κ.IsRegular := hReg
  let i (q : BoundedTrivialArrow Cᵣ Jᵣ κ) := (free Cᵣ).map q.val.2.2
  have hi (q : BoundedTrivialArrow Cᵣ Jᵣ κ) : W (i q) :=
    boundedTrivialGenerators_le Cᵣ Jᵣ κ _ ⟨q⟩
  have hS : ∀ ⦃A B : PointedSimplicialPresheaf.{u + 1} Cᵣ⦄ (f : A ⟶ B),
      W f → W ((tatePresheafSuspension R).map f) := by
    intro A B f hf
    exact stalkwiseTrivialMonomorphisms_smashRightFunctor_map Cᵣ Jᵣ (liftedTateSphere R) hf
  have h := projectiveLeft_le_levelwise_of_presentable (S := Sᵣ) W hS i hi
    (fun _ ↦ isPresentable_pointedSimplicialPresheaf _)
  change (levelwise (S := Sᵣ) (boundedTrivialGenerators Cᵣ Jᵣ κ).rlp).llp ≤
    levelwise W at h
  rw [rlp_boundedTrivialGenerators_eq Cᵣ Jᵣ hF κ hκ hFκ hC hPoint] at h
  exact h

/-- Levelwise fibrations which are levelwise weak equivalences are precisely
the levelwise maps lifting against all monomorphisms. -/
theorem tateLevelTrivialFibrations_eq :
    levelwise (S := Sᵣ) (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp =
      tateLevelFibrations R ⊓ tateLevelWeakEquivalences R := by
  ext X Y f
  constructor
  · intro h
    constructor
    · intro n A B j hj
      exact h n j hj.1
    · intro n
      exact stalkwiseWeakEquivalences_of_mono_rlp.{u + 1} Cᵣ Jᵣ (h n)
  · intro h n
    exact mono_rlp_of_weak_of_stalkwiseTrivial_rlp Cᵣ Jᵣ (h.2 n) (h.1 n)

/-- The projective cofibration and levelwise trivial-fibration classes factor
all strict Tate-prespectrum maps. -/
theorem tateProjective_hasFactorization :
    HasFactorization (tateProjectiveCofibrations R)
      (levelwise (S := Sᵣ) (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp) := by
  let T := Σ q : Cᵣᵒᵖ × SimplexCategoryᵒᵖ, Σ r : Cᵣᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r
  obtain ⟨κ, _, hT⟩ := HasCardinalLT.exists_regular_cardinal.{u + 1} T
  have hC (q : Cᵣᵒᵖ × SimplexCategoryᵒᵖ) :
      HasCardinalLT (Σ r : Cᵣᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ :=
    hT.of_injective (fun s ↦ (⟨q, s⟩ : T))
      (by intro _ _ e; exact eq_of_heq (Sigma.mk.inj_iff.1 e).2)
  let : HasFunctorialFactorization
      (levelwise (S := Sᵣ) (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp).llp
      (levelwise (S := Sᵣ) (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp) :=
    tateLevelMono_hasFunctorialFactorization R κ hC
  change HasFactorization (levelwise (S := Sᵣ) (monomorphisms
    (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp).llp _
  infer_instance

/-- The projective trivial-cofibration and levelwise fibration classes factor
all strict Tate-prespectrum maps. -/
theorem tateProjectiveTrivial_hasFactorization :
    HasFactorization (tateProjectiveTrivialCofibrations R) (tateLevelFibrations R) := by
  obtain ⟨F, hSmall, hF⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty Jᵣ
  let : ObjectProperty.Small.{u + 1} F := hSmall
  obtain ⟨κ, hReg, hκ, hFκ, hC, hPoint⟩ :=
    CategoryTheory.SimplicialSubpresheaf.exists_regular_cardinal_bounds (F := F)
  let : Fact κ.IsRegular := hReg
  let : HasFunctorialFactorization
      (levelwise (S := Sᵣ) (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp).llp
      (levelwise (S := Sᵣ) (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp) :=
    tateLevelStalkwiseFibration_hasFunctorialFactorization R hF κ hκ hFκ hC hPoint
  change HasFactorization (levelwise (S := Sᵣ)
    (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp).llp
    (levelwise (S := Sᵣ) (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp)
  infer_instance

/-- Projective cofibrations and levelwise trivial fibrations form a weak
factorization system. -/
theorem tateProjective_isWeakFactorizationSystem :
    IsWeakFactorizationSystem (tateProjectiveCofibrations R)
      (levelwise (S := Sᵣ) (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp) := by
  let : Functor.IsLeftAdjoint Sᵣ := (tatePresheafAdjunction R).isLeftAdjoint
  let : HasFactorization (tateProjectiveCofibrations R)
      (levelwise (S := Sᵣ) (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp) :=
    tateProjective_hasFactorization R
  have : (tateProjectiveCofibrations R).IsStableUnderRetracts := by
    change (levelwise (S := Sᵣ) (monomorphisms
      (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp).llp.IsStableUnderRetracts
    infer_instance
  apply IsWeakFactorizationSystem.mk'
  intro A B X Y i p hi hp
  exact hi p hp

/-- Projective trivial cofibrations and levelwise fibrations form a weak
factorization system. -/
theorem tateProjectiveTrivial_isWeakFactorizationSystem :
    IsWeakFactorizationSystem (tateProjectiveTrivialCofibrations R) (tateLevelFibrations R) := by
  let : Functor.IsLeftAdjoint Sᵣ := (tatePresheafAdjunction R).isLeftAdjoint
  let : HasFactorization (tateProjectiveTrivialCofibrations R) (tateLevelFibrations R) :=
    tateProjectiveTrivial_hasFactorization R
  have : (tateProjectiveTrivialCofibrations R).IsStableUnderRetracts := by
    change (levelwise (S := Sᵣ) (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp).llp.IsStableUnderRetracts
    infer_instance
  have : (tateLevelFibrations R).IsStableUnderRetracts := by
    change (levelwise (S := Sᵣ) (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp).IsStableUnderRetracts
    infer_instance
  apply IsWeakFactorizationSystem.mk'
  intro A B X Y i p hi hp
  exact hi p hp

/-- Projective trivial cofibrations are exactly the projective cofibrations
that are levelwise stalkwise weak equivalences. -/
theorem tateProjectiveTrivialCofibrations_eq :
    tateProjectiveTrivialCofibrations R =
      tateProjectiveCofibrations R ⊓ tateLevelWeakEquivalences R := by
  let : Functor.IsLeftAdjoint Sᵣ := (tatePresheafAdjunction R).isLeftAdjoint
  have hQ : levelwise (S := Sᵣ)
      (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp ≤
      tateLevelFibrations R := by
    intro X Y f hf n A B i hi
    exact hf n i hi.1
  have hC : tateProjectiveTrivialCofibrations R ≤ tateProjectiveCofibrations R :=
    antitone_llp hQ
  have hW : tateProjectiveTrivialCofibrations R ≤ tateLevelWeakEquivalences R := by
    intro X Y f hf n
    exact (tateProjectiveTrivialCofibrations_le_levelwiseTrivialMono R f hf n).2
  apply le_antisymm
  · exact le_inf hC hW
  · intro X Y f hf
    let : HasFactorization (tateProjectiveTrivialCofibrations R) (tateLevelFibrations R) :=
      tateProjectiveTrivial_hasFactorization R
    let d := factorizationData (tateProjectiveTrivialCofibrations R) (tateLevelFibrations R) f
    have : (tateLevelWeakEquivalences R).HasTwoOutOfThreeProperty := by
      change (levelwise (S := Sᵣ) (stalkwiseWeakEquivalences Cᵣ Jᵣ)).HasTwoOutOfThreeProperty
      infer_instance
    have hpW : tateLevelWeakEquivalences R d.p :=
      (tateLevelWeakEquivalences R).of_precomp d.i d.p (hW _ d.hi) (d.fac.symm ▸ hf.2)
    have hp : levelwise (S := Sᵣ)
        (monomorphisms (PointedSimplicialPresheaf.{u + 1} Cᵣ)).rlp d.p := by
      rw [tateLevelTrivialFibrations_eq R]
      exact ⟨d.hp, hpW⟩
    let : HasLiftingProperty f d.p := hf.1 d.p hp
    have : (tateProjectiveTrivialCofibrations R).IsStableUnderRetracts := by
      change (levelwise (S := Sᵣ)
        (stalkwiseTrivialMonomorphisms Cᵣ Jᵣ).rlp).llp.IsStableUnderRetracts
      infer_instance
    exact (tateProjectiveTrivialCofibrations R).of_retract
      (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

/-- The projective Nisnevich stalkwise level model structure on strict Tate
prespectra. Weak equivalences and fibrations are the specified levelwise
classes, and cofibrations are their projective left class. -/
@[instance_reducible]
def tateLevelModelCategory : HomotopicalAlgebra.ModelCategory Tᵣ := by
  let : Functor.IsLeftAdjoint Sᵣ := (tatePresheafAdjunction R).isLeftAdjoint
  let : HomotopicalAlgebra.CategoryWithFibrations Tᵣ := ⟨tateLevelFibrations R⟩
  let : HomotopicalAlgebra.CategoryWithCofibrations Tᵣ := ⟨tateProjectiveCofibrations R⟩
  let : HomotopicalAlgebra.CategoryWithWeakEquivalences Tᵣ := ⟨tateLevelWeakEquivalences R⟩
  let : HasFiniteLimits Tᵣ := by infer_instance
  let : HasFiniteColimits Tᵣ := by infer_instance
  let : (HomotopicalAlgebra.weakEquivalences Tᵣ).HasTwoOutOfThreeProperty := by
    change (levelwise (S := Sᵣ) (stalkwiseWeakEquivalences Cᵣ Jᵣ)).HasTwoOutOfThreeProperty
    infer_instance
  let : IsWeakFactorizationSystem (HomotopicalAlgebra.cofibrations Tᵣ)
      (HomotopicalAlgebra.trivialFibrations Tᵣ) := by
    change IsWeakFactorizationSystem (tateProjectiveCofibrations R)
      (tateLevelFibrations R ⊓ tateLevelWeakEquivalences R)
    rw [← tateLevelTrivialFibrations_eq R]
    exact tateProjective_isWeakFactorizationSystem R
  let : IsWeakFactorizationSystem (HomotopicalAlgebra.trivialCofibrations Tᵣ)
      (HomotopicalAlgebra.fibrations Tᵣ) := by
    change IsWeakFactorizationSystem
      (tateProjectiveCofibrations R ⊓ tateLevelWeakEquivalences R) (tateLevelFibrations R)
    rw [← tateProjectiveTrivialCofibrations_eq R]
    exact tateProjectiveTrivial_isWeakFactorizationSystem R
  exact HomotopicalAlgebra.ModelCategory.mk' Tᵣ

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-1233"]
  AlgebraicGeometry.MotivicHomotopy.tateLevelWeakEquivalences
  AlgebraicGeometry.MotivicHomotopy.tateLevelFibrations
  AlgebraicGeometry.MotivicHomotopy.tateProjectiveCofibrations
  AlgebraicGeometry.MotivicHomotopy.tateLevelModelCategory

attribute [colib_ref "Hovey2001Spectra" "Section 1, Theorem 1.14, pp. 7–8"
  "adaptation" "The projective level model structure for the actual Nisnevich classes"]
  AlgebraicGeometry.MotivicHomotopy.tateLevelModelCategory
