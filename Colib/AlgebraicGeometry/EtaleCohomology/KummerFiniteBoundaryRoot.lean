/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.KummerPicardSpecialization
public import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRoot

/-!
# Global tensor roots with prescribed finite-boundary compatibility

Proper Kummer specialization supplies an actual global root from a closed-fibre root.
The native pullback/tensor-power comparison and finite-boundary frame adjustment then give
an exact compatible frame for that root. The chosen fibre root need not extend, and the
boundary is not replaced by its reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible
open Stacks.EtaleCohomology

universe u

namespace Stacks.Kummer

local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- A closed-fibre tensor root gives a global root with a frame realizing the specified
boundary trivialization through the actual global root isomorphism. Both the global root
isomorphism and its full finite-boundary compatibility are part of the conclusion. -/
@[colib_tag "COL-1212"]
theorem exists_schemeTensorPower_iso_compatible_frame_of_closedFibre
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
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
          (Scheme.Modules.pullback i).mapIso α ≪≫ τ := by
  obtain ⟨M, hM, ⟨α⟩⟩ :=
    exists_schemeTensorPower_iso_of_closedFibre R f hn0 hX L hL M₀ hM₀ e₀
  exact ⟨M, hM, α, exists_root_compatible_frame_of_module_finite R B i M L hM hn α τ⟩

end Stacks.Kummer
