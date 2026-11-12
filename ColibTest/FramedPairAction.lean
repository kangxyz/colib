/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.FramedPairAction

/-! # Actual framed finite pairs have equal HI torsion actions on general smooth bases

No local coefficient ring occurs here. The given root, full-boundary frames,
finite section data and whole finite locally free divisors produce their original
principal correction by COL-1072. Its actual COL-1100 polynomial family kills
that correction on ordinary HI coefficients.
-/

noncomputable section

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

local instance regressionMovingTensorQuotientSecondInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N := hN.toAlgebraicGeometry

local instance regressionMovingTensorQuotientTensorInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorObj L N) :=
  (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
    L N).toAlgebraicGeometry

example
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
  exact transfer_framed_pair_eq i D E L N P hP A T j q hcover r hr hDU hEU hD hE k hn
    α e eN hcompat a b ha0 hb0 haB hbB haU hbU

end AlgebraicGeometry.PresheafWithTransfers

#print axioms AlgebraicGeometry.PresheafWithTransfers.transfer_framed_pair_eq
