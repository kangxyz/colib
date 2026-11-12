/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.RingTheory.Branches.MinimalPrimes

/-!
# Normality after the actual strict-local base change

A normal scheme over an affine base remains normal after an ind-etale base change. The proof
uses the actual inverse-image affine charts and native normality of their tensor-product rings.
Applying this after base change to the ordinary local ring proves normality after the canonical
`strictHenselizationToBase`. No finite-type or smooth-site condition is imposed on that limit.

The ring input is the native `isNormalRing_tensorProduct_of_ind_etale`; localization is handled
by the native `isNormal_of_flat_preimmersion`. These are preservation statements for normality,
not an assertion that strict-local base change preserves integrality or connectedness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Ind-etale base change of the base preserves normality of an arbitrary scheme over it. -/
theorem isNormal_pullback_of_indEtale
    (A R : Type u) [CommRing A] [CommRing R] [Algebra A R]
    (hind : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A R))
    {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) [IsNormal X] :
    IsNormal (pullback p (Spec.map (CommRingCat.ofHom (algebraMap A R)))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap A R))
  let π := pullback.fst p b
  apply ((isNormal_tfae (pullback p b)).out 4 1).mp
  refine ⟨X.affineOpens, fun U ↦ π ⁻¹ᵁ U.1, IsOpenCover.mk ?_, fun U ↦ ?_⟩
  · rw [← π.preimage_iSup, iSup_affineOpens_eq_top, π.preimage_top]
  · let : Algebra A Γ(X, U.1) :=
      (CommRingCat.ofHom (Scheme.ΓSpecIso (.of A)).inv.hom ≫
        p.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    have hnormal : IsNormalRing Γ(X, U.1) :=
      ((isNormal_tfae X).out 1 2 :
        IsNormal X ↔ ∀ V : X.affineOpens, IsNormalRing Γ(X, V)).mp ‹IsNormal X› U
    obtain ⟨E, -, -⟩ := exists_iso_pullback_ι_comp_SpecMap_tensorProduct A R X p U.1 U.2
    let E₁ : (π ⁻¹ᵁ U.1).toScheme ≅ pullback U.1.ι π :=
      (isPullback_morphismRestrict π U.1).isoPullback
    let E₂ : pullback U.1.ι π ≅ pullback (U.1.ι ≫ p) b :=
      pullbackRightPullbackFstIso p b U.1.ι
    have : IsNormal (Spec (.of (Γ(X, U.1) ⊗[A] R))) :=
      isNormal_spec_of_isNormalRing
        (isNormalRing_tensorProduct_of_ind_etale Γ(X, U.1) hnormal hind)
    exact isNormal_of_iso (E₁ ≪≫ E₂ ≪≫ E)

/-- The actual strict-henselization morphism is flat, using its native ind-etale local-ring
map followed by the ordinary local-spectrum morphism. -/
theorem flat_strictHenselizationToBase
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S) :
    Flat (strictHenselizationToBase B S hS s) := by
  have : Flat (Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, ← algebraMap_etaleLocalRing,
      RingHom.flat_algebraMap_iff]
    exact CommAlgCat.flat_of_ind_etale
      (StacksDraft.indEtale_iff.mp (indEtale_etaleLocalRing B S hS s))
  have := flat_fromSpecStalk S (s.hom (IsLocalRing.closedPoint s.residueField))
  dsimp [strictHenselizationToBase]
  infer_instance

/-- A normal scheme remains normal after pullback along the actual strict-henselization map.
The proof factors that map through the ordinary local ring and then uses its native ind-etale
extension; it does not regard the strict henselization as a smooth finite-type scheme. -/
theorem isNormal_pullback_strictHenselizationToBase
    (B : BigEtaleSite.{u}) {S X : Scheme.{u}} (hS : B.Contains S)
    (s : GeometricPoint S) (p : X ⟶ S) [IsNormal X] :
    IsNormal (pullback p (strictHenselizationToBase B S hS s)) := by
  let x := s.hom (IsLocalRing.closedPoint s.residueField)
  let i := S.fromSpecStalk x
  let a := Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS s))
  have : Flat i := flat_fromSpecStalk S x
  have : IsPreimmersion i := inferInstance
  have : IsNormal (pullback p i) := isNormal_of_flat_preimmersion (pullback.fst p i)
  have : IsNormal (pullback (pullback.snd p i) a) :=
    isNormal_pullback_of_indEtale _ _
      (StacksDraft.indEtale_iff.mp (indEtale_etaleLocalRing B S hS s))
      (pullback.snd p i)
  exact isNormal_of_iso (pullbackLeftPullbackSndIso p i a).symm

end AlgebraicGeometry
