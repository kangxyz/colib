/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.SameFibreSectionDivisorRoot

/-!
# Same-fibre section roots with a prescribed target and boundary frame

Proper Kummer specialization constructs a root of the actual difference of the two
section kernels. A specified isomorphism transports that root to the chosen target
module. Finite-boundary frame correction then realizes the specified trivialization
of that target, on the entire module-finite boundary including its nilpotents.

The original root is retained explicitly: the boundary equation uses its composite
with the specified target isomorphism. Thus the target may be the actual pullback of
an earlier-stage difference module, and its prescribed frame may be the pullback of
that stage's frame. No identification with the local canonical boundary frame is
needed. A root, initial root frame, or equality of transfer actions is not an input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.EtaleCohomology Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.Kummer

/-- The scheme structure sheaf has commutative multiplication on every open. -/
local instance sameFibrePrescribedFrameMulCommutative (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- The actual same-fibre section difference admits a root whose transport to a specified
isomorphic target has a frame realizing any specified full finite-boundary trivialization. -/
theorem exists_sameFibreSectionKernel_root_prescribed_frame
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X U : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : residueFieldPoint R ≫ s = residueFieldPoint R ≫ t)
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
    (i : Spec (CommRingCat.of B) ⟶ X) (L : X.Modules)
    (β : differenceSheaf s.ker t.ker ≅ L)
    (τ : (Scheme.Modules.pullback i).obj L ≅
      _root_.SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))))
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
      (α : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf s.ker t.ker),
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
          (Scheme.Modules.pullback i).mapIso (α ≪≫ β) ≪≫ τ := by
  obtain ⟨M, hM, ⟨α⟩⟩ :=
    exists_schemeTensorPower_iso_sameFibreSectionKernel_differenceSheaf
      R q j s t hs ht hsj htj hst hn0 hn
  exact ⟨M, hM, α,
    exists_root_compatible_frame_of_module_finite R B i M L hM hn (α ≪≫ β) τ⟩

end Stacks.Kummer
