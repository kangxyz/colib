/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor
public import Colib.RingTheory.Koszul.QuotientPair

/-!
# Degree-zero original pair Tor is the full incidence stalk

Both actual coefficient stalks are quotients of the ambient stalk by their
literal kernels. Native degree-zero Tor identifies their tensor product with
the quotient by the sum. The scheme-theoretic incidence kernel is exactly
this sum, with no radical or reduction. This constructs an actual ambient
module isomorphism; no regularity, Tor equality or multiplicity is assumed.

The algebraic input is `CategoryTheory.torZeroQuotientQuotientIso`, which uses
Mathlib's degree-zero derived tensor and quotient tensor product. The native
geometric input is `correspondenceIncidenceAmbientInclusion_ker`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The actual support quotient, with the original point transport and scalar map. -/
def correspondenceIncidenceSupportStalkQuotientIso
    (x : correspondenceIncidence f g h z w) :
    ModuleCat.of (correspondenceIncidenceAmbientStalk f g h z w x)
      (correspondenceIncidenceAmbientStalk f g h z w x ⧸
        RingHom.ker (correspondenceIncidenceSupportStalkMap f g h z w x)) ≅
      correspondenceIncidenceSupportStalkModule f g h z w x := by
  let A := correspondenceIncidenceAmbientStalk f g h z w x
  let D := (correspondenceSupportProduct f g h z w).presheaf.stalk
    (correspondenceIncidenceToSupportProduct f g h z w x)
  letI : Algebra A D := (correspondenceIncidenceSupportStalkMap f g h z w x).toAlgebra
  exact (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A D)
    (correspondenceIncidenceSupportStalkMap_surjective f g h z w x)).toLinearEquiv.toModuleIso

/-- The full incidence stalk kernel is the sum of the two literal coefficient kernels. -/
theorem correspondenceIncidenceAmbientStalkMap_ker [IsSeparated g]
    (x : correspondenceIncidence f g h z w) :
    RingHom.ker ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom =
      RingHom.ker (correspondenceIncidenceSupportStalkMap f g h z w x) ⊔
        RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
          (correspondenceIncidenceInclusion f g h z w x)).hom := by
  have hs : RingHom.ker (correspondenceIncidenceSupportStalkMap f g h z w x) =
      IdealSheafData.stalk (correspondenceSupportProductInclusion f g h z w).ker
        (correspondenceIncidenceAmbientInclusion f g h z w x) := by
    have aux (p : correspondenceIntersectionAmbient f g h)
        (hp : p = correspondenceSupportProductInclusion f g h z w
          (correspondenceIncidenceToSupportProduct f g h z w x)) :
        RingHom.ker (((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
          (.of_eq hp)).hom ≫ (correspondenceSupportProductInclusion f g h z w).stalkMap
            (correspondenceIncidenceToSupportProduct f g h z w x)).hom =
          IdealSheafData.stalk (correspondenceSupportProductInclusion f g h z w).ker p := by
      subst p
      simpa [TopCat.Presheaf.stalkCongr] using
        ker_stalkMap_eq_idealStalk_ker (correspondenceSupportProductInclusion f g h z w)
          (correspondenceIncidenceToSupportProduct f g h z w x)
    exact aux _ (correspondenceIncidence_ambient_point_eq f g h z w x)
  have hδ : RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
      (correspondenceIncidenceInclusion f g h z w x)).hom =
      IdealSheafData.stalk (correspondenceTripleInclusion f g h).ker
        (correspondenceIncidenceAmbientInclusion f g h z w x) :=
    ker_stalkMap_eq_idealStalk_ker (correspondenceTripleInclusion f g h)
      (correspondenceIncidenceInclusion f g h z w x)
  rw [hs, hδ, ker_stalkMap_eq_idealStalk_ker,
    correspondenceIncidenceAmbientInclusion_ker, IdealSheafData.stalk_sup, sup_comm]

/-- Native degree-zero ambient pair Tor is the full actual incidence stalk. -/
def correspondenceIncidenceAmbientTorZeroIso [IsSeparated g]
    (x : correspondenceIncidence f g h z w) :
    correspondenceIncidenceAmbientTor f g h z w x 0 ≅
      (ModuleCat.restrictScalars
        ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom).obj
        (ModuleCat.of ((correspondenceIncidence f g h z w).presheaf.stalk x)
          ((correspondenceIncidence f g h z w).presheaf.stalk x)) := by
  let A := correspondenceIncidenceAmbientStalk f g h z w x
  let C := (correspondenceIncidence f g h z w).presheaf.stalk x
  let I := RingHom.ker (correspondenceIncidenceSupportStalkMap f g h z w x)
  let J := RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
    (correspondenceIncidenceInclusion f g h z w x)).hom
  let κ := ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom
  letI : Algebra A C := κ.toAlgebra
  have hk : RingHom.ker κ = I ⊔ J := correspondenceIncidenceAmbientStalkMap_ker f g h z w x
  let eqC : ModuleCat.of A (A ⧸ I ⊔ J) ≅
      (ModuleCat.restrictScalars κ).obj (ModuleCat.of C C) := by
    rw [← hk]
    exact (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A C)
      (SurjectiveOnStalks.stalkMap_surjective
        (correspondenceIncidenceAmbientInclusion f g h z w) x)).toLinearEquiv.toModuleIso
  exact (((Tor (ModuleCat A) 0).mapIso
      (correspondenceIncidenceSupportStalkQuotientIso f g h z w x).symm).app
        (correspondenceIncidenceTripleStalkModule f g h z w x)) ≪≫
    ((Tor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I))).mapIso
      (correspondenceIncidenceDiagonalStalkQuotientIso f g h z w x).symm ≪≫
    CategoryTheory.torZeroQuotientQuotientIso A I J ≪≫ eqC

/-- Degree-zero length is exactly the full incidence local-ring length, including infinity. -/
theorem length_correspondenceIncidenceAmbientTor_zero [IsSeparated g]
    (x : correspondenceIncidence f g h z w) :
    Module.length (correspondenceIncidenceAmbientStalk f g h z w x)
      (correspondenceIncidenceAmbientTor f g h z w x 0) =
        Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
          ((correspondenceIncidence f g h z w).presheaf.stalk x) := by
  rw [(correspondenceIncidenceAmbientTorZeroIso f g h z w x).toLinearEquiv.length_eq]
  let κ := ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom
  let C := (correspondenceIncidence f g h z w).presheaf.stalk x
  let M := (ModuleCat.restrictScalars κ).obj (ModuleCat.of C C)
  let := κ.toAlgebra
  let : IsScalarTower (correspondenceIncidenceAmbientStalk f g h z w x) C M :=
    ⟨fun a b m => by
      change (κ a * b) • m = κ a • (b • m)
      exact mul_smul (κ a) b m⟩
  exact Module.length_eq_of_surjective (R := C) (M := M)
    (SurjectiveOnStalks.stalkMap_surjective
      (correspondenceIncidenceAmbientInclusion f g h z w) x)

/-- Restricting the canonical support action along the actual surjective ambient map
preserves length. -/
theorem correspondenceIncidenceTor_length_eq_support [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    letI := correspondenceIncidenceTorSupportModule f g h z w x n
    Module.length (correspondenceIncidenceAmbientStalk f g h z w x)
      (correspondenceIncidenceAmbientTor f g h z w x n) =
        Module.length ((correspondenceSupportProduct f g h z w).presheaf.stalk
          (correspondenceIncidenceToSupportProduct f g h z w x))
          (correspondenceIncidenceAmbientTor f g h z w x n) := by
  let := correspondenceIncidenceTorSupportModule f g h z w x n
  let := (correspondenceIncidenceSupportStalkMap f g h z w x).toAlgebra
  let := correspondenceIncidenceTorSupportScalarTower f g h z w x n
  exact Module.length_eq_of_surjective
    (correspondenceIncidenceSupportStalkMap_surjective f g h z w x)

/-- Degree-zero length over the actual support ring equals full incidence-ring length. -/
theorem length_correspondenceIncidenceAmbientTor_zero_support [IsSeparated g]
    (x : correspondenceIncidence f g h z w) :
    letI := correspondenceIncidenceTorSupportModule f g h z w x 0
    Module.length ((correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w x))
      (correspondenceIncidenceAmbientTor f g h z w x 0) =
        Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
          ((correspondenceIncidence f g h z w).presheaf.stalk x) := by
  let := correspondenceIncidenceTorSupportModule f g h z w x 0
  exact (correspondenceIncidenceTor_length_eq_support f g h z w x 0).symm.trans
    (length_correspondenceIncidenceAmbientTor_zero f g h z w x)

end Stacks.Chow
