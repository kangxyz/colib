/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Henselian.FiniteAlgebraUnits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.SemilocalFibre.Basic

/-!
# Adjusting a frame on a finite boundary

For `B` finite over a strictly henselian local ring `R`, every specified trivialization of
an invertible sheaf's `n`-th tensor power on `Spec B` is induced by a frame when `n` is
invertible in `R`. The equation is an equality of the
native sheaf isomorphisms on the entire `Spec B`, not an equality on its reduced scheme
or on residue-field points. The final specialization uses the actual module pullback
along a boundary morphism.

The adjustment lemmas retain an explicit initial frame. The final existence theorems
supply it using native semilocality, the trivial Picard group of a semilocal ring, and
the native affine invertible-sheaf triviality theorem. No framed Picard group or relative
cohomology comparison is introduced here.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.Invertible
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u v

namespace AlgebraicGeometry

local instance (S : Scheme.{v}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]

/-- A prescribed trivialization of a tensor power on a finite boundary is the tensor
power of an actual frame. The initial frame is given, rather than inferred from an
unproved semilocal triviality assertion. -/
@[colib_tag "COL-1032",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/EtaleCohomology/KummerTheory/Basic.lean:1049-1064,1128-1138"
    "ingredient" "The native trivialization ratio criterion and tensor-power composition"]
theorem exists_frame_tensorPowerMap_eq_of_module_finite {n : ℕ}
    (hn : IsUnit (n : R))
    (L : SheafOfModules.{v} (ringSheaf (Spec (CommRingCat.of B))))
    [IsInvertible (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) L]
    (e : L ≅ SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))))
    (α : tensorPower (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) L (n : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    ∃ e' : L ≅ SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e' n ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n = α := by
  let D := Spec (CommRingCat.of B)
  let β := tensorPowerMap D e n ≪≫ structureSheafTensorPowerIso D n
  let q := Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨b, hb⟩ :=
    StrictlyHenselianLocalRing.surjective_pow_units_of_module_finite R B hn
      (q (trivializationRatio D n α β))
  have hroot : trivializationRatio D n α β = (q.symm b) ^ n := by
    apply q.injective
    simpa only [map_pow, q.apply_symm_apply] using hb.symm
  obtain ⟨φ⟩ := (pairIso_iff_trivializationRatio_eq_pow D n L α β).mpr
    ⟨q.symm b, hroot⟩
  refine ⟨φ.sheafIso ≪≫ e, ?_⟩
  rw [tensorPowerMap_trans_eq, Iso.trans_assoc]
  exact φ.compatible

/-- The corrected frame on the actual pullback along a morphism from the finite affine
`R`-scheme `Spec B` satisfies the prescribed equation on the original boundary, including
its nilpotents. -/
@[colib_tag "COL-1032"]
theorem exists_pullback_frame_tensorPowerMap_eq_of_module_finite
    {C : Scheme.{v}} (i : Spec (CommRingCat.of B) ⟶ C) (L : C.Modules)
    [IsInvertible (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj L)]
    {n : ℕ} (hn : IsUnit (n : R))
    (e : (Scheme.Modules.pullback i).obj L ≅
      SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))))
    (α : tensorPower (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj L) (n : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    ∃ e' : (Scheme.Modules.pullback i).obj L ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e' n ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n = α :=
  exists_frame_tensorPowerMap_eq_of_module_finite R B hn _ e α

/-- Every prescribed tensor-power trivialization on `Spec B` admits an exact compatible
frame. Semilocal triviality supplies the initial frame, including when `B` is the zero ring. -/
@[colib_tag "COL-1032",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/SemilocalFibre/Basic.lean:151-155"
    "ingredient" "A module-finite algebra over a local ring is semilocal",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/PicardUFD/Affine.lean:101-125"
    "ingredient" "An invertible sheaf on Spec B is trivial when the ring Picard group is trivial"]
theorem exists_compatible_frame_of_module_finite {n : ℕ} (hn : IsUnit (n : R))
    (L : SheafOfModules.{v} (ringSheaf (Spec (CommRingCat.of B))))
    [hL : IsInvertible (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) L]
    (α : tensorPower (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) L (n : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    ∃ e : L ≅ SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e n ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n = α := by
  let : Finite (MaximalSpectrum B) :=
    Stacks.RingTheory.SemilocalModuleFinite.finite_maximalSpectrum_of_moduleFinite_of_isLocalRing
      R B
  let : Stacks.SheafOfModules.IsInvertible (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  obtain ⟨e⟩ := Stacks.PicardUFD.isTrivial_of_isInvertible_spec B L
  exact exists_frame_tensorPowerMap_eq_of_module_finite R B hn L e α

/-- An invertible actual pullback to the finite affine `R`-scheme `Spec B` has a frame
whose tensor power is the prescribed trivialization, without an initial-frame input. -/
@[colib_tag "COL-1032"]
theorem exists_compatible_pullback_frame_of_module_finite
    {C : Scheme.{v}} (i : Spec (CommRingCat.of B) ⟶ C) (L : C.Modules)
    [IsInvertible (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj L)]
    {n : ℕ} (hn : IsUnit (n : R))
    (α : tensorPower (Spec (CommRingCat.of B)).presheaf
      (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj L) (n : ℤ) ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    ∃ e : (Scheme.Modules.pullback i).obj L ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e n ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n = α :=
  exists_compatible_frame_of_module_finite R B hn _ α

end AlgebraicGeometry
