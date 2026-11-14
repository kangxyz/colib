/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModule
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The original roots-of-unity module over lifted coefficients

Restrict the scalar action of the existing roots-of-unity module along the actual
ring equivalence ULift(Z/n) → Z/n. The underlying abelian sheaf is unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Stacks.Kummer

variable (X : Scheme.{u}) (n : ℕ) [NeZero n]

/-- The original roots-of-unity module with its scalars read through the lift equivalence. -/
def rootsOfUnityULiftModule :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) :=
  ⟨(rootsOfUnityModule.{u, 0} X n).obj ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} (ZMod n) ≃+* ZMod n).toRingHom,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})
      (rootsOfUnitySheaf.{u, 0} X n).property⟩

variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})]

/-- Forgetting lifted coefficients recovers the original roots-of-unity abelian sheaf. -/
def rootsOfUnityULiftModuleForgetIso :
    (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})).obj
      (rootsOfUnityULiftModule X n) ≅ rootsOfUnitySheaf.{u, 0} X n := Iso.refl _

end Stacks.Kummer
