/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleCounitReduction

/-! # Algebraically closed residue-geometric detection of the actual counit

UNVERIFIED production integration wrapper; its existing predecessor is in the
repository, but this algebraically-closed wrapper still requires CI compilation.

This supporting reduction uses the native closed residue-geometric points.
It removes the need to extend an arbitrary separably closed marking field when
applying the geometric construction. The rigidity input remains a hypothesis.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{u + 1} k)

local instance : IsAffine (base (Spec (.of k))).left :=
  inferInstanceAs (IsAffine (Spec (.of k)))

/-- Native closed residue-geometric points already detect the counit. Thus the
rigidity input need only cover algebraically closed marking fields; no comparison
along an enlargement of a merely separably closed field is required. -/
theorem isIso_fullSmallEtale_sheafification_counit_iff_algebraicallyClosedSeparableNeighborhood
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)
    IsIso ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app F) ↔
      ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
        (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left),
        IsClosed ({ξ default} : Set X.left) →
          let : Algebra k (X.left.residueField (ξ default)) :=
            (fieldToResidue X.hom (ξ default)).hom.toAlgebra
          Algebra.IsSeparable k (X.left.residueField (ξ default)) →
            IsIso (etaleNeighborhoodValuePullback
              (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
                X ⟶ base (Spec (.of k))) (ξ := ξ) rfl ((toPresheaf k).obj P)) := by
  dsimp only
  constructor
  · intro hc
    let := hc
    intro X _ Ω _ _ ξ _ _
    apply (isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
      X ξ (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp))
        rfl ((toPresheaf k).obj P)).mp
    exact (inferInstance : IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).sheafFiber.map
      ((fullSmallEtaleAdjunction (base (Spec (.of k)))).counit.app
        ((presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
          AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)))))
  · intro hsep
    apply (isIso_iff_affineClosedResidueGeometricNeighborhoodValue _).mpr
    intro X _ x hx
    let Ω := (GeometricPoint.ofPoint X.left x).residueField
    let ξ : Spec (.of Ω) ⟶ X.left := (GeometricPoint.ofPoint X.left x).hom
    have hxMark : IsClosed ({ξ default} : Set X.left) := by
      change IsClosed ({(GeometricPoint.ofPoint X.left x).hom default} : Set X.left)
      rw [GeometricPoint.ofPoint_liesOver]
      exact hx
    rcases CharP.exists' k with hzero | ⟨p, hp, hk⟩
    · let := hzero
      let : Algebra k (X.left.residueField (ξ default)) :=
        (fieldToResidue X.hom (ξ default)).hom.toAlgebra
      have : Module.Finite k (X.left.residueField (ξ default)) :=
        finite_residueField_overField_of_isClosed X.hom (ξ default) hxMark
      exact (isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
        X ξ (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp))
        rfl ((toPresheaf k).obj P)).mpr (hsep X Ω ξ hxMark inferInstance)
    · let := hp
      let := hk
      obtain ⟨m, hc, hs, he⟩ :=
        exists_separable_closedPoint_counit_iff P p X ξ hxMark n hn hP
      apply he.mp
      let T := SmoothSite.nFoldFrobeniusTwist p (isInCharacteristic_spec k p) m X
      let η := ξ ≫ (SmoothSite.nFoldRelativeFrobenius p (isInCharacteristic_spec k p) m X).left
      exact (isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
        T η (homMk T.hom (by change T.hom ≫ 𝟙 _ = T.hom; simp))
          rfl ((toPresheaf k).obj P)).mpr (hsep T Ω η hc hs)

end AlgebraicGeometry.PresheafWithTransfers
