/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.HomotopyDescent

/-!
# Comparison and homotopy cancellation through the original double cylinder

The cylinder homotopy and the descended maps retain the original span and any
specified target. These are the topological assembly facts used after the
actual endpoint legs have been recognized as homotopy equivalences.

Adapted from the assembly in
`Quillen/Topology/PlusConstruction/ClassicalCWComparison.lean:65-90` and
`Quillen/Topology/PlusConstruction/ClassicalCWComparisonUniqueness.lean:39-116`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u

namespace TopCat.DoubleCylinder

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}

/-- Inverting the original right leg gives a comparison with its actual
under-source homotopy. The first homotopy uses the full original cylinder. -/
def comparisonUnderSourceOfLegEquivs
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (I : ContinuousMap.HomotopyEquiv B D) (J : ContinuousMap.HomotopyEquiv C D)
    (hI : I.toFun = gapLeftEndpoint e) (hJ : J.toFun = gapRightEndpoint e) :
    ((I.trans J.symm).toFun.comp f.hom).Homotopy g.hom := by
  let H := (ContinuousMap.Homotopy.refl J.invFun).comp (endpointHomotopy f g sq)
  have hs : J.invFun.comp ((gapLeftEndpoint e).comp f.hom) =
      (I.trans J.symm).toFun.comp f.hom :=
    congrArg (fun m : C(B, D) ↦ J.invFun.comp (m.comp f.hom)) hI.symm
  have ht : J.invFun.comp ((gapRightEndpoint e).comp g.hom) =
      (J.invFun.comp J.toFun).comp g.hom :=
    congrArg (fun m : C(C, D) ↦ J.invFun.comp (m.comp g.hom)) hJ.symm
  exact (H.cast hs ht).trans ((J.left_inv.some.compContinuousMap g.hom).cast rfl rfl)

variable {l₀ : A ⊗ TopCat.I ⟶ D} {e₀ : TopCat.of (B ⊕ B) ⟶ D}

/-- The two original self-cylinder inclusions are homotopic as soon as
the actual left inclusion has a homotopy inverse. -/
def selfEndHomotopyOfLeftLegEquiv
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f f) l₀ e₀)
    (I : ContinuousMap.HomotopyEquiv B D) (hI : I.toFun = gapLeftEndpoint e₀) :
    (gapLeftEndpoint e₀).Homotopy (gapRightEndpoint e₀) := by
  let q := selfFold f sq
  have hstart : q.comp (I.toFun.comp I.invFun) = I.invFun := by
    apply ContinuousMap.ext
    intro x
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, hI]
    exact ContinuousMap.congr_fun (selfFold_left f sq) (I.invFun x)
  let L : I.invFun.Homotopy q :=
    ((ContinuousMap.Homotopy.refl q).comp I.right_inv.some).cast hstart rfl
  have hleft : (I.toFun.comp q).comp (gapRightEndpoint e₀) = gapLeftEndpoint e₀ := by
    apply ContinuousMap.ext
    intro x
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, hI]
    exact congrArg (gapLeftEndpoint e₀) (ContinuousMap.congr_fun (selfFold_right f sq) x)
  let K : (I.toFun.comp q).Homotopy (ContinuousMap.id D) :=
    ((ContinuousMap.Homotopy.refl I.toFun).comp L.symm).trans I.right_inv.some
  exact (K.compContinuousMap (gapRightEndpoint e₀)).cast hleft rfl

/-- A homotopy after precomposition descends to the original maps into any
same-universe target, using the actual self-cylinder pushout and left leg. -/
def homotopyCancelOfLeftLegEquiv {Y : Type u} [TopologicalSpace Y]
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f f) l₀ e₀)
    (I : ContinuousMap.HomotopyEquiv B D) (hI : I.toFun = gapLeftEndpoint e₀)
    (h₀ h₁ : C(B, Y)) (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) : h₀.Homotopy h₁ :=
  ((ContinuousMap.Homotopy.refl (homotopyDesc f f sq h₀ h₁ H)).comp
    (selfEndHomotopyOfLeftLegEquiv f sq I hI)).cast
    (homotopyDesc_left f f sq h₀ h₁ H) (homotopyDesc_right f f sq h₀ h₁ H)

end TopCat.DoubleCylinder
