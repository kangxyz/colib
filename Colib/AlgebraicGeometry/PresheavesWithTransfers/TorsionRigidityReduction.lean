/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorsionNeighborhoodReduction
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.CounitBasePoint
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.AffineClosedPoints

/-! # From fixed-exponent rigidity to sectionwise torsion rigidity

This reduction isolates the subgroup and germ argument from the geometric proof
of fixed-exponent rigidity. Its fixed-exponent premise is supplied by that
existing geometric theorem in `EtaleRigidityTorsion`.
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

/-- Rigidity with a common invertible positive exponent implies rigidity for
sectionwise prime-to-characteristic torsion. This is the reduction used in
MVW Proposition 7.21, applied to the actual transfer subpresheaves and germs. -/
theorem isIso_counit_of_sectionwiseTorsion_of_fixedExponentRigidity
    (P : PresheafWithTransfers.{u + 1} k) (hA : IsA1Invariant P)
    (hT : IsPrimeToCharacteristicTorsion P)
    (hfixed : ∀ (Q : PresheafWithTransfers.{u + 1} k), IsA1Invariant Q →
      ∀ (n : ℕ), (∀ (V : SmoothSite (Spec (.of k)))
        (z : sections Q ((Cor.graphFunctor k).obj V)), (n + 1) • z = 0) →
      IsUnit ((n + 1 : ℕ) : k) →
      let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj ((toPresheaf.{u + 1} k).obj Q)
      IsIso ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F)) :
    let F := (presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj ((toPresheaf.{u + 1} k).obj P)
    IsIso ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F) := by
  apply (isIso_iff_affineClosedEtaleNeighborhoodValue _).mpr
  intro X _ Ω _ _ ξ _
  apply (isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
    X ξ (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp)) rfl
    ((toPresheaf.{u + 1} k).obj P)).mpr
  apply isIso_structuralPullback_of_torsionSubpresheaf_pullbacks P hT _ X ξ
  intro n hn Y _ Ω' _ _ η
  have hc := hfixed (torsionSubpresheaf P (n + 1))
    (isA1Invariant_torsionSubpresheaf P hA (n + 1)) n
    (fun V z => torsionSubpresheaf_nsmul P (n + 1) _ z) hn
  apply (isIso_fullSmallEtale_sheafification_counit_iff_structuralNeighborhoodPullback
    Y η (homMk Y.hom (by change Y.hom ≫ 𝟙 _ = Y.hom; simp)) rfl
    ((toPresheaf.{u + 1} k).obj (torsionSubpresheaf P (n + 1)))).mp
  let := hc
  change IsIso ((etaleNeighborhoodPoint.{u, u + 1} Y η).sheafFiber.map
    ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app
      ((presheafToSheaf (SmoothSite.etaleTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj
          ((toPresheaf.{u + 1} k).obj (torsionSubpresheaf P (n + 1))))))
  infer_instance

end AlgebraicGeometry.PresheafWithTransfers
