/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.IteratedFrobenius
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodPullbackFunctor
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.CounitBasePoint

/-!
# Actual Frobenius transport of neighborhood restrictions and the canonical counit

The original torsion presheaf with transfers remains on the original smooth site.
Native étale base change gives cofinality of actual marked neighborhoods. Each
actual projection is finite flat radicial, so its original graph restriction is
invertible by the existing transfers. The resulting colimit map is precisely the
original marked pullback, not an unspecified isomorphism between its endpoints.
The canonical counit is transported using its proved native-base naturality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius Stacks.EtaleCohomology
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}

omit [IsSepClosed Ω] in
/-- Each original neighborhood projection is genuinely the base change of the given
finite flat universal homeomorphism, and its original PST restriction is invertible. -/
theorem isIso_etaleNeighborhoodPullback_projection (q : X ⟶ Y) (h : ξ ≫ q.left = η)
    [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ))
    (B : SmoothSite.EtaleNeighborhood Y η) :
    IsIso (((toPresheaf k).obj P).map (etaleNeighborhoodPullbackHom q h B).op) := by
  have : IsFinite (etaleNeighborhoodPullbackHom q h B).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (etaleNeighborhoodPullback_isPullback q h B)
      inferInstance
  have : Flat (etaleNeighborhoodPullbackHom q h B).left :=
    MorphismProperty.of_isPullback (P := @Flat) (etaleNeighborhoodPullback_isPullback q h B)
      inferInstance
  have : UniversalHomeomorphism (etaleNeighborhoodPullbackHom q h B).left := by
    constructor
    intro A C j₁ j₂ g hg
    exact UniversalHomeomorphism.universally_isHomeomorph _ _ _
      (hg.flip.paste_horiz (etaleNeighborhoodPullback_isPullback q h B)).flip
  exact isIso_toPresheaf_map_of_universalHomeomorphism P _ n hn hP

/-- Native site equivalence plus genuine original projection restrictions give
invertibility of the specified original marked neighborhood pullback. -/
theorem isIso_etaleNeighborhoodValuePullback_of_radicial (q : X ⟶ Y) (h : ξ ≫ q.left = η)
    [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
    [(smallEtaleBaseChange q.left).IsEquivalence]
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    IsIso (etaleNeighborhoodValuePullback q h ((toPresheaf k).obj P)) := by
  have : ∀ B, IsIso (((toPresheaf k).obj P).map (etaleNeighborhoodPullbackHom q h B).op) :=
    isIso_etaleNeighborhoodPullback_projection P q h n hn hP
  exact isIso_etaleNeighborhoodValuePullback q h ((toPresheaf k).obj P)

/-- The actual sheafification unit preserves the proved original radicial pullback. -/
theorem isIso_sheafification_etaleNeighborhoodValuePullback_of_radicial
    (q : X ⟶ Y) (h : ξ ≫ q.left = η)
    [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
    [(smallEtaleBaseChange q.left).IsEquivalence]
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    IsIso (etaleNeighborhoodValuePullback q h
      (sheafify (SmoothSite.etaleTopology (Spec (.of k))) ((toPresheaf k).obj P))) := by
  have := isIso_etaleNeighborhoodValuePullback_of_radicial P q h n hn hP
  rw [← isIso_comp_left_iff (etaleNeighborhoodSheafificationIso Y η ((toPresheaf k).obj P)).hom,
    etaleNeighborhoodSheafificationIso_hom_pullback]
  infer_instance

/-- The actual canonical counit is transported through its native-base naturality square.
The original pullback is supplied by genuine marked cofinality and transfer inverses. -/
theorem isIso_counit_iff_of_radicial (q : X ⟶ Y) (h : ξ ≫ q.left = η)
    [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
    [(smallEtaleBaseChange q.left).IsEquivalence]
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} Y η).presheafFiber.map
      ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom) ↔
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
      ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom) := by
  dsimp only
  let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
    AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)
  have := isIso_sheafification_etaleNeighborhoodValuePullback_of_radicial P q h n hn hP
  have hnatur := fullSmallEtale_counit_nativeBase_marked_naturality Y η q ξ h F
  have he := congrArg IsIso hnatur
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using (iff_of_eq he)

/-- The original marked pullback along the literal n-fold relative Frobenius is invertible.
This uses the native small-site Frobenius equivalence and actual pullback projections. -/
@[colib_tag "COL-1111", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/FrobeniusDescent.lean:164-169"
  "ingredient" "Native absolute Frobenius small-site isomorphism; actual relative Frobenius \
    marked cofinality and original PST colimit pullback are assembled here."]
theorem isIso_nFoldRelativeFrobenius_etaleNeighborhoodValuePullback
    (p : ℕ) [Fact p.Prime] (hk : IsInCharacteristic (Spec (.of k)) p) (m : ℕ)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (ξ : Spec (.of Ω) ⟶ X.left) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    IsIso (etaleNeighborhoodValuePullback (SmoothSite.nFoldRelativeFrobenius p hk m X)
      (ξ := ξ) rfl ((toPresheaf k).obj P)) := by
  have := smallEtaleBaseChange_nFoldRelativeFrobenius_isEquivalence p hk m X
  exact isIso_etaleNeighborhoodValuePullback_of_radicial P _ rfl n hn hP

/-- Frobenius transports the genuine canonical counit at the actual image of the marking.
No rigidity conclusion at the image point is assumed or asserted. -/
@[colib_tag "COL-1111", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/FrobeniusDescent.lean:164-169"
  "ingredient" "Native absolute Frobenius site isomorphism; marked cofinality, actual PST \
    neighborhood pullback and canonical counit transport are proved here."]
theorem isIso_counit_iff_nFoldRelativeFrobenius
    (p : ℕ) [Fact p.Prime] (hk : IsInCharacteristic (Spec (.of k)) p) (m : ℕ)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (ξ : Spec (.of Ω) ⟶ X.left) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    let Y := SmoothSite.nFoldFrobeniusTwist p hk m X
    let η := ξ ≫ (SmoothSite.nFoldRelativeFrobenius p hk m X).left
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} Y η).presheafFiber.map
      ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom) ↔
    IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
      ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom) := by
  have := smallEtaleBaseChange_nFoldRelativeFrobenius_isEquivalence p hk m X
  exact isIso_counit_iff_of_radicial P _ rfl n hn hP

/-- At every original closed geometric marking, an actual finite Frobenius twist has
separable closed residue, and invertibility of the genuine counit is equivalent there.
This is the arbitrary-field transport step, not the separable-residue rigidity step. -/
@[colib_tag "COL-1111"]
theorem exists_separable_closedPoint_counit_iff
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (ξ : Spec (.of Ω) ⟶ X.left) (hx : IsClosed ({ξ default} : Set X.left))
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    ∃ m : ℕ,
      let T := SmoothSite.nFoldFrobeniusTwist p (isInCharacteristic_spec k p) m X
      let q := SmoothSite.nFoldRelativeFrobenius p (isInCharacteristic_spec k p) m X
      let η := ξ ≫ q.left
      letI : Algebra k (T.left.residueField (η default)) :=
        (fieldToResidue T.hom (η default)).hom.toAlgebra
      let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)
      IsClosed ({η default} : Set T.left) ∧
        Algebra.IsSeparable k (T.left.residueField (η default)) ∧
        (IsIso ((etaleNeighborhoodPoint.{u, u + 1} T η).presheafFiber.map
          ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom) ↔
        IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
          ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F).hom)) := by
  obtain ⟨m, hc, hs, _⟩ :=
    exists_separable_closedPoint_iteratedFrobenius_iso P p X (ξ default) hx n hn hP
  refine ⟨m, hc, hs, ?_⟩
  exact isIso_counit_iff_nFoldRelativeFrobenius P p (isInCharacteristic_spec k p) m X ξ n hn hP

end AlgebraicGeometry.PresheafWithTransfers
