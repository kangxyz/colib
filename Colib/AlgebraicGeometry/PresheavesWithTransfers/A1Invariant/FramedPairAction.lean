/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.BoundaryUnitAction
public import Colib.AlgebraicGeometry.Correspondences.Divisors.FramedMovingRelation

/-! # Actual framed finite pairs have equal HI torsion actions on general smooth bases

No local coefficient ring occurs here. The given root, full-boundary frames,
finite section data and whole finite locally free divisors produce their original
principal correction by COL-1072. Its actual COL-1100 polynomial family kills
that correction on ordinary HI coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Chow
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules (schemeTensorPower)

universe u v

attribute [local instance] Stacks.Morphisms.IsFiniteLocallyFree.isFinite
  Stacks.Morphisms.IsFiniteLocallyFree.flat
  Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite
  PrincipalFamilyUnitOpen

attribute [local instance] framedCorrectionInvertible framedCorrectionQuasicoherent
  framedCorrectionDifferenceInvertible framedCorrectionDifferenceAGInvertible
  framedCorrectionPullbackInvertible framedCorrectionPullbackAGInvertible
  framedCorrectionMulCommutative framedCorrectionTensorEquivalence framedCorrectionPowerInvertible

variable {X B : Scheme.{u}} [IsIntegral X] (i : B ⟶ X)
  (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
  (L N : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
  [hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N]

local instance movingTensorQuotientSecondInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N := hN.toAlgebraicGeometry

local instance movingTensorQuotientTensorInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorObj L N) :=
  (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

/-- Given actual framed finite pairs, their original native divisor correspondences
have equal actions. The principal correction is constructed, not a supplied homotopy. -/
@[colib_ref "motivic_source_3df0a472"
  "Motivic/Transfers/Presheaf/Actions/Principal/Family.lean:52-69"
  "adaptation"
  "original HI principal-action ingredient combined with the actual framed finite-pair \
  construction and torsion cancellation on general smooth bases; no henselian descent claim",
  colib_tag "COL-1105"]
theorem transfer_framed_pair_eq
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    (A T : SmoothSite (Spec (.of K))) [IsAffine A.left] [IsIntegral A.left]
    [IsNoetherian X] [Nonempty B]
    {U : Scheme.{u}} [IsNoetherian U] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [U.IsQuasiAffine]
    (q : X ⟶ A.left) [IsProper q] [SmoothOfRelativeDimension 1 (j ≫ q)]
    [IsIntegral (parameterSpace (q ≫ A.hom))]
    [IsNoetherian (parameterSpace (q ≫ A.hom))]
    (hcover : (Set.range j)ᶜ ⊆ Set.range i)
    (r : U ⟶ Limits.pullback A.hom T.hom)
    (hr : r ≫ Limits.pullback.fst A.hom T.hom = j ≫ q)
    (hDU : Set.range D.subschemeι ⊆ Set.range j)
    (hEU : Set.range E.subschemeι ⊆ Set.range j)
    [Stacks.Morphisms.IsFiniteLocallyFree (D.subschemeι ≫ q)]
    [Stacks.Morphisms.IsFiniteLocallyFree (E.subschemeι ≫ q)]
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (k : ℕ) (hn : ∀ x : sections P ((Cor.graphFunctor K).obj A), (k + 1) • x = 0)
    (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf D E)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (ringSheaf B))
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (hcompat : tensorPowerMap B e (k + 1) ≪≫ structureSheafTensorPowerIso B (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫
        differenceSheafBoundaryIso i D E hD hE)
    (a : Γ(tensorObj L N, ⊤)) (b : N.sections) (ha0 : a ≠ 0) (hb0 : b.eval (op ⊤) ≠ 0)
    (haB : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(B, ⊤)))
    (hbB : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) =
      (1 : Γ(B, ⊤)))
    (haU : Set.range (zeroScheme X (tensorObj L N) a).subschemeι ⊆ Set.range j)
    (hbU : Set.range (zeroScheme X N (b.eval (op ⊤))).subschemeι ⊆ Set.range j)
    [Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X (tensorObj L N) a).subschemeι ≫ q)]
    [Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X N (b.eval (op ⊤))).subschemeι ≫ q)] :
    transfer P (show (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T from
      retainedFiniteFlatDivisorCorrespondence A.hom T.hom q j r hr D hDU) =
    transfer P (show (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T from
      retainedFiniteFlatDivisorCorrespondence A.hom T.hom q j r hr E hEU) := by
  let : IsAffine ((𝟭 Scheme).obj A.left) := ‹IsAffine A.left›
  let : IsIntegral ((𝟭 Scheme).obj A.left) := ‹IsIntegral A.left›
  obtain ⟨Z, hrel, hZ, hbound⟩ := exists_retainedFiniteCorrespondence_tensorQuotientPower
    i D E L N j A.hom T.hom q r hr hDU hEU hD hE k α e eN hcompat a b ha0 hb0
    haB hbB haU hbU
  let S₀ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T :=
    retainedFiniteFlatDivisorCorrespondence A.hom T.hom q j r hr D hDU
  let T₀ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T :=
    retainedFiniteFlatDivisorCorrespondence A.hom T.hom q j r hr E hEU
  let D₁ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T :=
    retainedFiniteFlatDivisorCorrespondence A.hom T.hom q j r hr
      (zeroScheme X (tensorObj L N) a) haU
  let D₂ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T :=
    retainedFiniteFlatDivisorCorrespondence A.hom T.hom q j r hr
      (zeroScheme X N (b.eval (op ⊤))) hbU
  let Z₀ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T := Z
  have hrel₀ : S₀ - T₀ = (k + 1) • (D₁ - D₂) + Z₀ := hrel
  let z := r ≫ Limits.pullback.snd A.hom T.hom
  have hz : j ≫ q ≫ A.hom = z ≫ T.hom := by
    rw [← Category.assoc, ← hr, Category.assoc, Limits.pullback.condition]
    simp only [z, Category.assoc]
  have hrz : retainedCurveMap A.hom T.hom q j z hz = r := by
    apply Limits.pullback.hom_ext
    · exact (Limits.pullback.lift_fst (j ≫ q) z hz).trans hr.symm
    · exact Limits.pullback.lift_snd (j ≫ q) z hz
  have hzero := transfer_boundaryNormalized_rationalUnit_eq_zero P hP A T q j i hcover z hz
    _ hbound Z₀ (by
      change Z.val = _
      rw [hrz]
      exact hZ)
  change transfer P S₀ = transfer P T₀
  apply sub_eq_zero.mp
  rw [← transfer_sub, hrel₀, transfer_add, hzero, add_zero]
  have hmul : transfer P ((k + 1) • (D₁ - D₂)) = (k + 1) • transfer P (D₁ - D₂) :=
    P.obj.map_nsmul
  rw [hmul]
  ext x
  exact hn _

end AlgebraicGeometry.PresheafWithTransfers
