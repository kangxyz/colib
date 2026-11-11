/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift

/-!
# Finite pushforward and native flat cycle pullback

For a finite morphism, every residue field extension is finite. The dimension
filter in the native proper pushforward is therefore always satisfied, so its
underlying cycle is exactly `finiteCyclePushforward`, including every residue
degree. This comparison is between two existing operations on the same native
`AlgebraicCycle`, not between different cycle representations.

In a Cartesian square with a finite vertical map and a flat horizontal map of
constant relative dimension, Stacks 02RG consequently gives an identity of the
underlying native cycles. A coefficient specialization places each original point
in its own dimension grade. It keeps both flat-pullback multiplicities and all
finite residue degrees, including inseparable degrees and colliding images.

The cycle-level theorem is the native Stacks flat base-change identity, with its
coherence hypotheses discharged by finite direct-image coherence (01Y6), and its
base-change hypothesis by affine base change (02KG), since every finite morphism
is affine. These inputs are at commit
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
The dimension comparison is in `Chow/DominantPrimeCycle.lean:90-102` at the same
commit. No Tor comparison or correspondence composition theorem is a dependency.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}

/-- Finite proper pushforward has the same underlying cycle as native ungraded finite
pushforward: the actual residue degrees are retained and the dimension filter disappears. -/
@[stacks 02R4 "comparison of native graded proper pushforward with ungraded finite pushforward"]
theorem properPushforward_val_eq_finiteCyclePushforward
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsFinite f] (hf : f ≫ sY = sX)
    (k : ℤ) (α : CycleGroup C sX k) :
    (properPushforward C sX sY f hf k α).val = finiteCyclePushforward f α.val := by
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hdim (x : X) : relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sY (f.base x) := by
    rw [← hf]
    exact relativeDimension_eq_of_finite_residueField C.dimensionFunction sY f x
      (residueField_finite_of_locallyQuasiFinite f x)
  simp only [properPushforward_apply, finiteCyclePushforward_apply, hdim, ite_true]

/-- Finite direct images are coherent and commute with this base change. -/
private theorem isCoherent_and_isIso_of_isFinite
    (f : X ⟶ Y) [IsFinite f] (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    [IsLocallyNoetherian Y]
    [IsLocallyNoetherian X'] [IsLocallyNoetherian Y'] [IsFinite f']
    (F : X.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent ∧
    ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent ∧
    IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F) := by
  have : ((Scheme.Modules.pullback g').obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback g' F
  let :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  exact ⟨
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite f F,
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite f' _,
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsq F⟩

/-- Stacks 02RG as an equality of the actual ungraded native cycles, with the graded
flat pullbacks retained. The finite map, not an ambient projection, is proper. -/
@[stacks 02RG "finite vertical map; equality of the underlying native cycles"]
theorem finiteCyclePushforward_flatPullback
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsFinite f]
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (k : ℤ) (α : CycleGroup C sX k) :
    letI : IsFinite f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    finiteCyclePushforward f'
        (flatPullback C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k α).val =
      (flatPullback C sY' sY g hg r hgr k
        (properPushforward C sX sY f hf k α)).val := by
  let : IsFinite f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian sY'
  have H := flatPullback_properPushforward C sX sY sX' sY'
    f g g' f' hsq hf hg hg' r hgr k α
    (fun _ => (isCoherent_and_isIso_of_isFinite f g g' f' hsq _).1)
    (fun _ => (isCoherent_and_isIso_of_isFinite f g g' f' hsq _).2.1)
    (fun _ => (isCoherent_and_isIso_of_isFinite f g g' f' hsq _).2.2)
  have Hval := congrArg (fun β : CycleGroup C sY' (k + (r : ℤ)) => β.val) H
  rw [properPushforward_val_eq_finiteCyclePushforward] at Hval
  exact Hval.symm

/-- The coefficient identity for one original point in its own dimension grade. The
right-hand side includes all points above the specified target point, with their actual
residue degrees; no injectivity or degree-one assumption is present. -/
@[stacks 02RG "fixed-point coefficient formula with native flat weights and residue degrees"]
theorem finite_flatBaseChange_fixedLabel
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsFinite f]
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (x : X) (y' : Y') (hy' : g y' = f x) :
    let d := relativeDimension C.dimensionFunction sX x
    (f.residueDegree x : ℤ) * flatPullbackWeight C sY' g (d + (r : ℤ)) y' =
      ∑ᶠ x' ∈ f'.base ⁻¹' {y'},
        if g' x' = x then
          flatPullbackWeight C sX' g' (d + (r : ℤ)) x' * (f'.residueDegree x' : ℤ)
        else 0 := by
  classical
  let : IsFinite f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let d := relativeDimension C.dimensionFunction sX x
  let α : CycleGroup C sX d :=
    ⟨Function.locallyFinsuppWithin.single x (1 : ℤ), by
      rw [mem_cyclesOfDimension_iff_forall_point]
      intro a ha
      have hax : a = x := by
        by_contra hax
        exact ha (by simp [Function.locallyFinsuppWithin.single_apply, hax])
      subst a
      rfl⟩
  have H := finiteCyclePushforward_flatPullback C sX sY sX' sY'
    f g g' f' hsq hf hg hg' r hgr d α
  have He := congrArg (fun β : AlgebraicCycle Y' ℤ => β y') H
  rw [finiteCyclePushforward_apply, flatPullback_apply,
    properPushforward_val_eq_finiteCyclePushforward,
    finiteCyclePushforward_single] at He
  simpa only [flatPullback_apply, α, Function.locallyFinsuppWithin.single_apply,
    hy', ite_true, one_mul, ite_mul, zero_mul] using He.symm

end Stacks.Chow
