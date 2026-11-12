/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.AffineClosedPoint
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.FiniteField.Affine
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.RestrictionMono

/-! # Actual finite-field coefficient local-zero input and dense restriction

Geometric local vanishing gives the coefficient input at universe `u + 1`.
For Nisnevich sheaves with transfers it gives zero detection and monicity of
dense-open restriction.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/FiniteField/CoefficientLocalZero.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `27a67b7ef20524924a89d5183ae3e85ee36ea307`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

/-- Actual finite-field geometry supplies the original integral-affine coefficient input. -/
theorem integralAffineLocalZero_of_finite (k : Type u) [Field k] [Finite k] :
    IntegralAffineLocalZero k := by
  apply integralAffineLocalZero_of_affineClosedPoint
  intro B _ _ _ _ x _ J hJ d hd A _ a _ ha hcover P hP s hs
  exact exists_finite_affine_zero_neighborhood_of_positive_trdeg
    k B x J hJ d hd a ha hcover P hP s hs

end AlgebraicGeometry.PresheafWithTransfers

namespace AlgebraicGeometry.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

/-- A section of an original HI Nisnevich sheaf over a finite field is detected
by its actual dense-open restriction. Separatedness is used only at this stage. -/
theorem section_eq_zero_of_dense_open_of_finite
    {k : Type u} [Field k] [Finite k] {X A : SmoothSite (Spec (.of k))}
    (a : A ⟶ X) [IsOpenImmersion a.left] (ha : DenseRange a.left)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (s : F.obj.sections (Cor.mk X))
    (hs : F.obj.transfer ((Cor.graphFunctor k).map a) s = 0) : s = 0 :=
  section_eq_zero_of_dense_open_of_integralAffineLocalZero
    (PresheafWithTransfers.integralAffineLocalZero_of_finite k) a ha F hF s hs

end AlgebraicGeometry.SheafWithTransfers

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

/-- The literal small-site restriction of an original HI Nisnevich sheaf to a
dense open is monic over a finite field. -/
theorem restrictionToDirectImage_mono_of_dense_of_finite
    {k : Type u} [Field k] [Finite k]
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (hj : DenseRange j.left) :
    Mono (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F) j) :=
  restrictionToDirectImage_mono_of_dense_of_integralAffineLocalZero
    (PresheafWithTransfers.integralAffineLocalZero_of_finite k) j F hF hj

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
