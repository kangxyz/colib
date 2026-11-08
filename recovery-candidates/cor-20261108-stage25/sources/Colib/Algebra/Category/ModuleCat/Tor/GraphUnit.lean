/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.FlatRestriction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import StacksFrontier.Homology.Tor.Presentation

/-!
# Tor coefficients for a flat ring retraction

Let `a : R →+* S` be flat and let `q : S →+* R` satisfy `q.comp a = RingHom.id R`.
For an arbitrary `R`-module `M`, the native categorical Tor modules of `R` (as an
`S`-module via `q`) and `S ⊗[R] M` vanish in every positive degree. In degree zero,
there is an isomorphism to `M` with its full `S`-action through `q`.

Only `a` is assumed flat. Neither `M` nor `q` is assumed flat. The degree-zero
statement does not require flatness at all. These are algebraic inputs to graph
unit calculations, not geometric incidence or correspondence unit laws.

The proof uses the native Tor object, the one-sided flat change-of-rings
isomorphism, the existing flat-module Tor vanishing theorem, and Mathlib's tensor
base-change cancellation and right-exact degree-zero derived-functor comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

namespace ModuleCat.Tor

variable {R S : Type u} [CommRing R] [CommRing S]
  (a : R →+* S) (q : S →+* R) (hqa : q.comp a = RingHom.id R)

/-- Cancelling scalar extension along a ring retraction retains the full `S`-action. -/
def graphUnitTensorIso (M : ModuleCat.{u} R) :
    ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R)) ⊗
        ((ModuleCat.extendScalars a).obj M) ≅
      (ModuleCat.restrictScalars q).obj M := by
  let : Algebra R S := a.toAlgebra
  let : Module S R := Module.compHom R q
  let : IsScalarTower R S R := ⟨fun r s x => by
    change q (a r * s) * x = r * (q s * x)
    rw [q.map_mul, show q (a r) = r from DFunLike.congr_fun hqa r, mul_assoc]⟩
  let : Module S M := Module.compHom M q
  let e : R ⊗[R] M ≃ₗ[S] M :=
    { __ := (TensorProduct.lid R M).toAddEquiv
      map_smul' := by
        intro s x
        change (TensorProduct.lid R M) (s • x) = q s • (TensorProduct.lid R M) x
        induction x using TensorProduct.inductionOn with
        | tmul r m =>
          change (q s * r) • m = q s • (r • m)
          exact mul_smul (q s) r m
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  exact LinearEquiv.toModuleIso
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S R M).trans e)

/-- Degree-zero graph Tor identifies with the support module, as an actual `S`-module. -/
def graphUnitTorZeroIso (M : ModuleCat.{u} R) :
    ((CategoryTheory.Tor (ModuleCat.{u} S) 0).obj
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R))).obj
        ((ModuleCat.extendScalars a).obj M) ≅
      (ModuleCat.restrictScalars q).obj M := by
  let N := (ModuleCat.restrictScalars q).obj (ModuleCat.of R R)
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft N) :=
    (ihom.adjunction N).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (tensorLeft N) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact ((tensorLeft N).leftDerivedZeroIsoSelf.app
    ((ModuleCat.extendScalars a).obj M)) ≪≫ graphUnitTensorIso a q hqa M

include hqa in
/-- Graph Tor has no positive degrees when the section is flat, for arbitrary support modules. -/
theorem isZero_graphUnitTor_succ (ha : a.Flat) (M : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} S) (n + 1)).obj
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R))).obj
        ((ModuleCat.extendScalars a).obj M)) := by
  let e : (ModuleCat.restrictScalars a).obj
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R)) ≅ ModuleCat.of R R :=
    (ModuleCat.restrictScalarsComp'App a q (RingHom.id R) hqa.symm
      (ModuleCat.of R R)).symm ≪≫
      ModuleCat.restrictScalarsId'App (RingHom.id R) rfl (ModuleCat.of R R)
  have hzero : IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) (n + 1)).obj
      ((ModuleCat.restrictScalars a).obj
        ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R)))).obj M) :=
    IsZero.of_iso (isZero_Tor_succ_of_flat (ModuleCat.of R R) M n)
      (((CategoryTheory.Tor (ModuleCat.{u} R) (n + 1)).mapIso e).app M)
  have hrestricted := IsZero.of_iso hzero
    (flatRestrictionIso a ha ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R))
      M (n + 1)).symm
  have hs := ModuleCat.subsingleton_of_isZero hrestricted
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

end ModuleCat.Tor
