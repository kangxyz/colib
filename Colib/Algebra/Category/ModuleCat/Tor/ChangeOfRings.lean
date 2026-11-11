/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.RingTheory.Tor.FlatExtendScalarsFirst

/-!
# Change of rings for Tor under coefficientwise Tor vanishing

For commutative rings and modules in one arbitrary common universe, an arbitrary
ring map `f : R →+* B`, an actual `R`-module `M`, and an actual `B`-module `N`,
positive-degree vanishing of `Tor_n^R(Res_f B, M)` gives

`Tor_n^R(Res_f N, M) ≅ Res_f Tor_n^B(N, B ⊗_R M)`

for every `n : ℕ`, including zero. The target is the restriction of the existing
`B`-module Tor, not a new scalar action on a replacement Tor model. Neither
flatness of `f` nor projectivity or flatness of `M` or `N` is assumed.

We extend a native natural-number projective resolution of `M`. Its augmentation
is a quasi-isomorphism by the public tensor-resolution theorem, detected by exact
conservative restriction of scalars. The native extension/restriction adjunction
preserves projective objects. The all-degree comparison then takes homology of
the inverse projection formula `n ⊗ m ↦ n ⊗ (1 ⊗ m)` and uses the two native
resolution computations of Tor. The projection formula in the other direction
sends `n ⊗ (b ⊗ m)` to `(b • n) ⊗ m`.

## Source references

* AxiomMath/Stacks, commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`,
  `StacksFrontier/Homology/Tor/IndependenceBaseChange.lean:169-177`: public
  positive-Tor vanishing criterion for the tensor of a resolution augmentation.
* At the same commit, `StacksFrontier/RingTheory/Tor/FlatExtendScalarsFirst.lean:60-64`:
  the unconditional native projection formula. Its flat-dependent Tor theorem is not used.
  The tensor formula is recorded in `StacksFrontier/Homology/KFlat/BaseChange.lean:121-132,219-226`.
* At the same commit, `StacksFrontier/Homology/ExtendScalars/Flat.lean:32-42`:
  additivity of native extension of scalars, with no flatness hypothesis.
* Mathlib, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`,
  `Mathlib/CategoryTheory/Abelian/LeftDerived.lean:110-117`: computation using a
  chosen projective resolution, and `Mathlib/Algebra/Homology/QuasiIso.lean:281-284`:
  reflection of quasi-isomorphisms by an exact conservative functor.
* At the same Mathlib commit, `Mathlib/CategoryTheory/Preadditive/Projective/Basic.lean:202-209`:
  projectivity under an adjunction with an epimorphism-preserving right adjoint;
  `Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean:449-454`:
  the homology comparison for exact restriction of scalars.

This is an all-degree assembly of those public inputs. It does not import the
upper `IndependenceTransitivity` application or duplicate its quasi-isomorphism
argument. No Stacks Project tag for regular sequences is attributed to this lemma.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace ModuleCat.Tor

variable {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)

/-- If the positive `Tor^R(B,M)` vanish, native extension of scalars carries a
projective resolution of `M` to a projective resolution of its actual extension. -/
def extendedProjectiveResolutionOfIsZeroTor {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M)
    (h : ∀ n : ℕ, 0 < n → IsZero
      (((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))).obj M)) :
    ProjectiveResolution ((ModuleCat.extendScalars.{u, u, u} f).obj M) where
  complex := ((ModuleCat.extendScalars f).mapHomologicalComplex (.down ℕ)).obj P.complex
  projective n := (ModuleCat.extendRestrictScalarsAdj f).map_projective _ (P.projective n)
  π := ((ModuleCat.extendScalars f).mapHomologicalComplex (.down ℕ)).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.extendScalars f) (.down ℕ) 0).hom.app M
  quasiIso := by
    have hr : QuasiIso (((ModuleCat.restrictScalars f).mapHomologicalComplex (.down ℕ)).map
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.down ℕ)).map P.π)) := by
      change QuasiIso (((tensorLeft ((ModuleCat.restrictScalars f).obj
        (ModuleCat.of B B))).mapHomologicalComplex (.down ℕ)).map P.π)
      exact RingTheory.TorIndependence.quasiIso_tensor_map_projectiveResolution_of_isZero_Tor
        _ _ P h
    have := (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
      (ModuleCat.restrictScalars f)).1 hr
    infer_instance

/-- Every-degree `R`-linear change of rings under positive vanishing of
`Tor^R(B,M)`, with the genuine restricted `B`-module Tor as target. -/
def changeOfRingsIsoOfIsZeroTor (N : ModuleCat.{u} B) (M : ModuleCat.{u} R)
    (h : ∀ i : ℕ, 0 < i → IsZero
      (((CategoryTheory.Tor (ModuleCat.{u} R) i).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))).obj M)) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars f).obj N)).obj M ≅
      (ModuleCat.restrictScalars f).obj
        (((CategoryTheory.Tor (ModuleCat.{u} B) n).obj N).obj
          ((ModuleCat.extendScalars.{u, u, u} f).obj M)) := by
  let P := projectiveResolution M
  let Q := extendedProjectiveResolutionOfIsZeroTor f P h
  let K := ((tensorLeft N).mapHomologicalComplex (.down ℕ)).obj Q.complex
  exact P.isoLeftDerivedObj (tensorLeft ((ModuleCat.restrictScalars f).obj N)) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℕ) n).mapIso
      ((NatIso.mapHomologicalComplex
        (Stacks.TorFlatExtendScalars.tensorExtendScalarsIso f N) (.down ℕ)).app
          P.complex).symm ≪≫
    (K.sc n).mapHomologyIso (ModuleCat.restrictScalars f) ≪≫
    (ModuleCat.restrictScalars f).mapIso (Q.isoLeftDerivedObj (tensorLeft N) n).symm

end ModuleCat.Tor
