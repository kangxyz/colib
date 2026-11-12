module

import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRoot
import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotientBoundary

/-!
# Tests for compatible finite-boundary frames of actual tensor roots
-/

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u v

local instance (S : Scheme.{v}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]

-- A nonzero square-zero boundary section is allowed; independent universes are retained.
example {X : Scheme.{v}} (i : Spec (CommRingCat.of B) ⟶ X) (M L : X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (b : B) (_hb : b ^ 2 = 0) (_hb0 : b ≠ 0)
    (hn : IsUnit (6 : R))
    (α : Stacks.SheafOfModules.schemeTensorPower X M hM (6 : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback i).obj L ≅
      SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    letI := hM
    letI : SheafOfModules.IsInvertible (Spec (CommRingCat.of B)).presheaf
        (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj M) :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
        (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom M)
    ∃ e : (Scheme.Modules.pullback i).obj M ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e 6 ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) 6 =
      (Scheme.Modules.pullbackIntegerTensorPowerIso i M hM (6 : ℤ)).symm ≪≫
        (Scheme.Modules.pullback i).mapIso α ≪≫ τ :=
  exists_root_compatible_frame_of_module_finite R B i M L hM hn α τ

-- Exponent 1: the root is global, and both maps in its boundary equation are retained.
example {X : Scheme.{v}} (i : Spec (CommRingCat.of B) ⟶ X) (M L : X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (α : Stacks.SheafOfModules.schemeTensorPower X M hM (1 : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback i).obj L ≅
      SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    letI := hM
    letI : SheafOfModules.IsInvertible (Spec (CommRingCat.of B)).presheaf
        (ringSheafCond (Spec (CommRingCat.of B))) ((Scheme.Modules.pullback i).obj M) :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
        (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom M)
    ∃ e : (Scheme.Modules.pullback i).obj M ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e 1 ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) 1 =
      (Scheme.Modules.pullbackIntegerTensorPowerIso i M hM (1 : ℤ)).symm ≪≫
        (Scheme.Modules.pullback i).mapIso α ≪≫ τ :=
  exists_root_compatible_frame_of_module_finite R B i M L hM (by simp) α τ

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackIntegerTensorPowerIso
#print axioms AlgebraicGeometry.exists_root_compatible_frame_of_module_finite
