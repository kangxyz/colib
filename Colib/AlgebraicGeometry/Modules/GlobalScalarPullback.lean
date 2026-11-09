/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishing
import Colib.Util.References

/-! # Global scalar multiplication and arbitrary geometric pullback

The action is the native `Stacks.RegularSequence.globalSmulCenter`. Pushforward compatibility
is the naturality of the structure-sheaf map on each open. The pullback equation follows by
the actual pullback-pushforward adjunction, without a flatness hypothesis.

Adapted from Quillen's `Modules/Scalar/Pullback.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RegularSequence (globalSmulCenter)
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Pushforward retains multiplication by the original global scalar under restriction of scalars.
-/
theorem globalSmulCenter_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : Γ(Y, ⊤)) (M : X.Modules) :
    (globalSmulCenter Y r).app ((Scheme.Modules.pushforward f).obj M) =
      (Scheme.Modules.pushforward f).map ((globalSmulCenter X (f.appTop r)).app M) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let m' : M.val.obj (op (f ⁻¹ᵁ U.unop)) := m
  let : Module (Γ(X, f ⁻¹ᵁ U.unop)) (M.val.obj (op (f ⁻¹ᵁ U.unop))) :=
    inferInstanceAs (Module (X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ U.unop)))
      (M.val.obj (op (f ⁻¹ᵁ U.unop))))
  change (f.app U.unop) (Y.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r) • m' =
    X.presheaf.map (homOfLE (show f ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op (f.appTop r) • m'
  congr 1
  exact ConcreteCategory.congr_hom (f.naturality
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op) r

/-- Geometric pullback maps the original scalar to its pulled-back scalar. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Modules/Scalar/Pullback.lean:22-54"
  "adaptation" "Native global scalar compatibility with arbitrary geometric pullback"]
theorem pullback_map_globalSmulCenter {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : Γ(Y, ⊤)) (M : Y.Modules) :
    (Scheme.Modules.pullback f).map ((globalSmulCenter Y r).app M) =
      (globalSmulCenter X (f.appTop r)).app ((Scheme.Modules.pullback f).obj M) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
    (Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).map
      ((globalSmulCenter Y r).app M) = _
  rw [← (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality]
  rw [← globalSmulCenter_pushforward]
  exact ((globalSmulCenter Y r).naturality _).symm

end AlgebraicGeometry.Scheme.Modules
