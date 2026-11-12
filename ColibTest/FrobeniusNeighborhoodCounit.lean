/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleNeighborhoodRadicial

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Frobenius Stacks.EtaleCohomology

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

-- The actual native site functor, including exponent zero, not a replacement functor.
example {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)
    (X : SmoothSite S) :
    (smallEtaleBaseChange (SmoothSite.nFoldRelativeFrobenius p hS 0 X).left).IsEquivalence :=
  smallEtaleBaseChange_nFoldRelativeFrobenius_isEquivalence p hS 0 X

-- Markings remain actual lifts even before assuming separable closedness.
example {A B : Scheme.{u}} (f : A ⟶ B) {Ω : Type u} [Field Ω]
    (ζ : Spec (.of Ω) ⟶ A) (ξ : Spec (.of Ω) ⟶ B) (h : ζ ≫ f = ξ)
    [(smallEtaleBaseChange f).IsEquivalence] :
    (markedEtaleBaseChange f ζ ξ h).IsEquivalence :=
  markedEtaleBaseChange_isEquivalence f ζ ξ h

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (p : ℕ) [Fact p.Prime] (hk : IsInCharacteristic (Spec (.of k)) p) (m : ℕ)
  (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left)
  (n : ℕ) (hn : IsUnit (n : k))
  (hP : ∀ W : SmoothSite (Spec (.of k)),
    Module.IsTorsionBy ℤ (PresheafWithTransfers.sections P (Cor.mk W)) (n : ℤ))

-- No separate affine-twist assumption is needed.
example : IsAffine (SmoothSite.nFoldFrobeniusTwist p hk m X).left := inferInstance

example : (etaleNeighborhoodPullbackFunctor
    (SmoothSite.nFoldRelativeFrobenius p hk m X) (ξ := ξ) rfl).Initial := by
  have := smallEtaleBaseChange_nFoldRelativeFrobenius_isEquivalence p hk m X
  exact etaleNeighborhoodPullbackFunctor_initial _ rfl

-- The invertible map is literally the original COL1093 neighborhood pullback.
example : IsIso (etaleNeighborhoodValuePullback (SmoothSite.nFoldRelativeFrobenius p hk m X)
    (ξ := ξ) rfl ((PresheafWithTransfers.toPresheaf k).obj P)) :=
  PresheafWithTransfers.isIso_nFoldRelativeFrobenius_etaleNeighborhoodValuePullback
    P p hk m X ξ n hn hP

-- It is also the actual cofinal colimit comparison, not merely an isomorphic pair of objects.
example :
    let q := SmoothSite.nFoldRelativeFrobenius p hk m X
    ∃ e : etaleNeighborhoodValue _ (ξ ≫ q.left) ((PresheafWithTransfers.toPresheaf k).obj P) ≅
      etaleNeighborhoodValue X ξ ((PresheafWithTransfers.toPresheaf k).obj P),
      e.hom = etaleNeighborhoodValuePullback q rfl ((PresheafWithTransfers.toPresheaf k).obj P) := by
  have := PresheafWithTransfers.isIso_nFoldRelativeFrobenius_etaleNeighborhoodValuePullback
    P p hk m X ξ n hn hP
  dsimp only
  exact ⟨asIso (etaleNeighborhoodValuePullback (SmoothSite.nFoldRelativeFrobenius p hk m X)
    (ξ := ξ) rfl ((PresheafWithTransfers.toPresheaf k).obj P)), rfl⟩

-- The actual full-small adjunction counit at the image marking is transported back.
example :
    let Y := SmoothSite.nFoldFrobeniusTwist p hk m X
    let η := ξ ≫ (SmoothSite.nFoldRelativeFrobenius p hk m X).left
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((PresheafWithTransfers.toPresheaf k).obj P)
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} Y η).presheafFiber.map
      ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom) ↔
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
      ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom) :=
  PresheafWithTransfers.isIso_counit_iff_nFoldRelativeFrobenius P p hk m X ξ n hn hP

-- Every original closed marking reaches an actual separable-residue closed image.
example [CharP k p] (hx : IsClosed ({ξ default} : Set X.left)) :
    ∃ r : ℕ,
      let T := SmoothSite.nFoldFrobeniusTwist p (isInCharacteristic_spec k p) r X
      let q := SmoothSite.nFoldRelativeFrobenius p (isInCharacteristic_spec k p) r X
      let η := ξ ≫ q.left
      letI : Algebra k (T.left.residueField (η default)) :=
        (fieldToResidue T.hom (η default)).hom.toAlgebra
      let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj ((PresheafWithTransfers.toPresheaf k).obj P)
      IsClosed ({η default} : Set T.left) ∧
        Algebra.IsSeparable k (T.left.residueField (η default)) ∧
        (IsIso ((etaleNeighborhoodPoint.{u, u + 1} T η).presheafFiber.map
          ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom) ↔
        IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
          ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom)) :=
  PresheafWithTransfers.exists_separable_closedPoint_counit_iff P p X ξ hx n hn hP

#print axioms smallEtaleBaseChangeFullyFaithful
#print axioms smallEtaleBaseChange_absoluteFrobeniusPow_essSurj
#print axioms smallEtaleBaseChange_nFoldRelativeFrobenius_isEquivalence
#print axioms etaleBaseChangeMark
#print axioms markedEtaleBaseChangeFullyFaithful
#print axioms markedEtaleBaseChange_essSurj
#print axioms markedEtaleBaseChange_isEquivalence
#print axioms etaleNeighborhoodPullbackFunctor
#print axioms etaleNeighborhoodPullbackSmallNatIso
#print axioms etaleNeighborhoodPullbackFunctor_initial
#print axioms etaleNeighborhoodPullbackIso_hom
#print axioms isIso_etaleNeighborhoodValuePullback
#print axioms PresheafWithTransfers.isIso_etaleNeighborhoodPullback_projection
#print axioms PresheafWithTransfers.isIso_etaleNeighborhoodValuePullback_of_radicial
#print axioms PresheafWithTransfers.isIso_counit_iff_of_radicial
#print axioms PresheafWithTransfers.isIso_nFoldRelativeFrobenius_etaleNeighborhoodValuePullback
#print axioms PresheafWithTransfers.isIso_counit_iff_nFoldRelativeFrobenius
#print axioms PresheafWithTransfers.exists_separable_closedPoint_counit_iff
