/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleNeighborhoodRadicial
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.AffineClosedPoints

/-!
# Global counit reduction to original separable-residue restrictions

For a presheaf with transfers on the original smooth site over an arbitrary field,
annihilated on every original object by a natural number invertible in the field
acting through its integer cast, the actual full-small/smooth counit is invertible
exactly when its original structural
marked-neighborhood pullbacks are invertible at affine closed separable-residue
markings. Closed residues are finite over the original field. In characteristic
zero they are separable; in positive characteristic the original relative Frobenius
transports the actual counit to a closed separable-residue marking. Affine closed
geometric conservativity then gives the global conclusion.

The displayed original restriction condition is the remaining geometric rigidity
obligation. It is not proved here, and no homotopy-invariant rigidity theorem is
asserted. In particular, the source remains the actual base marked-neighborhood
colimit, not the value of a substituted presheaf over an extension field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Frobenius

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)

local instance : IsAffine (base (Spec (.of k))).left :=
  inferInstanceAs (IsAffine (Spec (.of k)))

/-- The global actual counit is reduced to the original structural pullbacks at affine
closed separable-residue markings. The latter is an explicit remaining rigidity condition. -/
@[colib_tag "COL-1114", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/CharP/Defs.lean:256-260" "ingredient"
  "Native characteristic-zero or prime-characteristic alternative",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/FieldTheory/Separable.lean:655-664" "ingredient"
    "Native separability of integral extensions in characteristic zero; original finite \
      residues, actual Frobenius counit transport and global conservativity are assembled here"]
theorem isIso_fullSmallEtale_sheafification_counit_iff_separableClosedNeighborhood
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)
    IsIso ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F) ↔
      ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
        (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left),
        IsClosed ({ξ default} : Set X.left) →
          let : Algebra k (X.left.residueField (ξ default)) :=
            (fieldToResidue X.hom (ξ default)).hom.toAlgebra
          Algebra.IsSeparable k (X.left.residueField (ξ default)) →
            IsIso (etaleNeighborhoodValuePullback
              (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
                X ⟶ base (Spec (.of k))) (ξ := ξ) rfl ((toPresheaf k).obj P)) := by
  dsimp only
  constructor
  · intro hc X _ Ω _ _ ξ _ _
    apply (isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
      X ξ (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp))
        rfl ((toPresheaf k).obj P)).mp
    exact (inferInstance : IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).sheafFiber.map
      ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app
        ((presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
          AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)))))
  · intro hsep
    apply (isIso_iff_affineClosedEtaleNeighborhoodValue _).mpr
    intro X _ Ω _ _ ξ hx
    rcases CharP.exists' k with hzero | ⟨p, hp, hk⟩
    · let := hzero
      let : Algebra k (X.left.residueField (ξ default)) :=
        (fieldToResidue X.hom (ξ default)).hom.toAlgebra
      have : Module.Finite k (X.left.residueField (ξ default)) :=
        finite_residueField_overField_of_isClosed X.hom (ξ default) hx
      exact (isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
        X ξ (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp))
        rfl ((toPresheaf k).obj P)).mpr (hsep X Ω ξ hx inferInstance)
    · let := hp
      let := hk
      obtain ⟨m, hc, hs, he⟩ :=
        exists_separable_closedPoint_counit_iff P p X ξ hx n hn hP
      apply he.mp
      let T := SmoothSite.nFoldFrobeniusTwist p (isInCharacteristic_spec k p) m X
      let η := ξ ≫ (SmoothSite.nFoldRelativeFrobenius p (isInCharacteristic_spec k p) m X).left
      exact (isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
        T η (homMk T.hom (by change T.hom ≫ 𝟙 _ = T.hom; simp))
          rfl ((toPresheaf k).obj P)).mpr (hsep T Ω η hc hs)

/-- The same explicit original restriction condition places the actual étale sheafification
in the essential image of the actual extension from the full small étale site. -/
@[colib_tag "COL-1114", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Adjunction/FullyFaithful.lean:209-211" "specialization"
  "Native essential-image consequence of the actual adjunction counit's invertibility"]
theorem fullSmallEtaleExtend_essImage_sheafification_of_separableClosedNeighborhood
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ))
    (hsep : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
      (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left),
      IsClosed ({ξ default} : Set X.left) →
        let : Algebra k (X.left.residueField (ξ default)) :=
          (fieldToResidue X.hom (ξ default)).hom.toAlgebra
        Algebra.IsSeparable k (X.left.residueField (ξ default)) →
          IsIso (etaleNeighborhoodValuePullback
            (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
              X ⟶ base (Spec (.of k))) (ξ := ξ) rfl ((toPresheaf k).obj P))) :
    (fullSmallEtaleExtend (base (Spec (.of k)))).essImage
      ((presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)) := by
  have := (isIso_fullSmallEtale_sheafification_counit_iff_separableClosedNeighborhood
    P n hn hP).mpr hsep
  exact (fullSmallEtaleAdjunction (base (Spec (.of k)))).mem_essImage_of_counit_isIso _

end AlgebraicGeometry.PresheafWithTransfers
