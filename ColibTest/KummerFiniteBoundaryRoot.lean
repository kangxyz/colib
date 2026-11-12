module

import Colib.AlgebraicGeometry.EtaleCohomology.KummerFiniteBoundaryRoot

/-!
# Tests for proper Kummer roots with exact boundary compatibility
-/

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
open Stacks.EtaleCohomology
open Stacks.Kummer

universe u

local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

-- The conclusion keeps the actual global root map and the entire boundary frame equation.
example
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Scheme.Spec (.of R)) [IsProper f]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
    (i : Spec (CommRingCat.of B) ⟶ X)
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R))
    (hX : IsUnit (n : Γ(X, ⊤)))
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (τ : (Scheme.Modules.pullback i).obj L ≅
      _root_.SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))))
    (M₀ : (closedFibre R f).Modules)
    (hM₀ : Stacks.SheafOfModules.IsInvertible (closedFibre R f).presheaf
      (closedFibre R f).ringCatIsSheaf M₀)
    (e₀ : Stacks.SheafOfModules.schemeTensorPower (closedFibre R f) M₀ hM₀ (n : ℤ) ≅
      (Scheme.Modules.pullback (closedFibreInclusion R f)).obj L) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
      (α : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅ L),
      letI := hM
      letI : AlgebraicGeometry.SheafOfModules.IsInvertible
          (Spec (CommRingCat.of B)).presheaf (ringSheafCond (Spec (CommRingCat.of B)))
          ((Scheme.Modules.pullback i).obj M) :=
        Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
          (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom M)
      ∃ e : (Scheme.Modules.pullback i).obj M ≅
          _root_.SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
        tensorPowerMap (Spec (CommRingCat.of B)) e n ≪≫
          structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n =
        (Scheme.Modules.pullbackIntegerTensorPowerIso i M hM (n : ℤ)).symm ≪≫
          (Scheme.Modules.pullback i).mapIso α ≪≫ τ :=
  exists_schemeTensorPower_iso_compatible_frame_of_closedFibre R f B i hn0 hn hX L hL τ M₀ hM₀ e₀

#print axioms Stacks.Kummer.exists_schemeTensorPower_iso_compatible_frame_of_closedFibre
