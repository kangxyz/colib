/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.PlusConstruction.DisplayedComparisonChains
import Mathlib.GroupTheory.Perm.Basic

/-! # Actual maps and tracks of the displayed plus comparison -/
noncomputable section
open Topology CategoryTheory FundamentalGroupoid
universe u v t w

section MixedFundamentalGroups
variable {X : Type u} {Y : Type v} {Z : Type t}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
  {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
  (N : Subgroup (HomotopyGroup.Pi 1 X x))
  (hf : IsPlusConstruction.{u, v, w} f γ N)
  (hg : IsPlusConstruction.{u, t, w} g δ N)

example : displayedComparisonPath f g k H γ δ =
    (γ.map k.continuous).symm.trans ((H.evalAt x).trans δ) := rfl

example : (basedPiOneMap k (displayedComparisonPath f g k H γ δ)).comp
    (basedPiOneMap f γ) = basedPiOneMap g δ :=
  basedPiOneMap_displayedComparison f g k H γ δ

example : Function.Bijective (HomotopyGroup.piMap 0 k (x := y) rfl) :=
  IsPlusConstruction.displayedComparison_piOne_bijective f g k H γ δ N hf hg

example : Function.Injective (HomotopyGroup.piMap 0 k (x := y) rfl) :=
  (IsPlusConstruction.displayedComparison_piOne_bijective f g k H γ δ N hf hg).1

example : Function.Surjective (HomotopyGroup.piMap 0 k (x := y) rfl) :=
  (IsPlusConstruction.displayedComparison_piOne_bijective f g k H γ δ N hf hg).2

example : (basedPiOneMap f γ).ker = (HomotopyGroup.piMap 0 f (x := x) rfl).ker :=
  basedPiOneMap_ker f γ
end MixedFundamentalGroups

section OriginalChains
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
  {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
  (N : Subgroup (HomotopyGroup.Pi 1 X x))
  (hf : IsPlusConstruction.{u, u, u} f γ N) (hg : IsPlusConstruction.{u, u, u} g δ N)
  (A : LocalCoefficients.System.{u, u} Z)

example : QuasiIso (LocalCoefficients.UniverseLift.chainMap.{u, u, u} k A) :=
  IsPlusConstruction.displayedComparison_twisted_quasiIso f g k H γ δ N hf hg A

example (n : ℕ) : IsIso (LocalCoefficients.UniverseLift.homologyMap k A n) := by
  have := IsPlusConstruction.displayedComparison_twisted_quasiIso f g k H γ δ N hf hg A
  change IsIso (HomologicalComplex.homologyMap (LocalCoefficients.UniverseLift.chainMap k A) n)
  infer_instance

example (n : ℕ)
    (hf' : IsIso (LocalCoefficients.pushforwardHomologyMap f (LocalCoefficients.pullback k A) n))
    (hg' : IsIso (LocalCoefficients.pushforwardHomologyMap g A n)) :
    IsIso (LocalCoefficients.pushforwardHomologyMap k A n) :=
  LocalCoefficients.isIso_pushforwardHomologyMap_of_displayed_factorization f g k H A n hf' hg'
end OriginalChains

example {G : Type u} {J : Type v} {K : Type t} [Group G] [Group J] [Group K]
    (f : G →* J) (g : G →* K) (h : J →* K)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.ker = g.ker) (hcomm : h.comp f = g) : Function.Bijective h :=
  MonoidHom.bijective_of_surjective_equal_kernels f g h hf hg hker hcomm

example : ∃ σ τ : Equiv.Perm (Fin 3), σ * τ ≠ τ * σ :=
  ⟨Equiv.swap 0 1, Equiv.swap 1 2, by decide⟩
