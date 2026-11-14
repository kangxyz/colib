/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleRigidityCounit
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorsionRigidityReduction

/-! # Suslin rigidity for prime-to-characteristic torsion

No common annihilator is required. Each original presheaf section lies in a
fixed-exponent transfer subpresheaf. Original neighborhood representatives and
refinements pass the fixed-exponent rigidity theorem to the whole presheaf.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable {k : Type u} [Field k]
local instance : IsAffine (SmoothSite.base (Spec (.of k))).left :=
  inferInstanceAs (IsAffine (Spec (.of k)))

/-- Suslin rigidity: the étale sheafification of a homotopy-invariant,
prime-to-characteristic torsion presheaf with transfers is locally constant
in the sense of MVW Definition 6.7. No common exponent is assumed. -/
@[colib_tag "COL-1222", colib_ref "MVW2006"
  "Lecture 7, Theorem 7.20 and Proposition 7.21, pp. 51-52" "adaptation"
  "Sectionwise invertible annihilators; finite-exponent transfer subpresheaves and original germs"]
theorem isIso_fullSmallEtale_sheafification_counit_of_primeToCharacteristicTorsion
    (P : PresheafWithTransfers.{u + 1} k) (hA : IsA1Invariant P)
    (hT : IsPrimeToCharacteristicTorsion P) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf k).obj P)
    IsIso ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F) :=
  isIso_counit_of_sectionwiseTorsion_of_fixedExponentRigidity P hA hT
    (isIso_fullSmallEtale_sheafification_counit_of_A1Invariant k)

end AlgebraicGeometry.PresheafWithTransfers
