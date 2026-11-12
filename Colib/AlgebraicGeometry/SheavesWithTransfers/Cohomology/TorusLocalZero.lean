/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.ContractionGenericZero
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.GenericOpenVanishing
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Field

/-!
# Local vanishing of positive torus cohomology

The actual torus sections of positive ordinary cohomology with transfers vanish
locally on the original small Nisnevich site when that cohomology is A¹-invariant.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SheafCohomology

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers

variable {k : Type u} [Field k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Positive torus cohomology vanishes on a Nisnevich covering sieve of each
actual small-site neighborhood. -/
theorem torus_zeroSieve_mem_succ
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) (U : EtaleSeparatedFiniteType X.left)
    (s : ((EtaleSeparatedFiniteType.toSmoothSite X).op ⋙ (toPresheaf k).obj
      (torusSections (withTransfers k F (n + 1)))).obj (op U)) :
    Presheaf.equalizerSieve s 0 ∈ EtaleSeparatedFiniteType.nisnevichTopology X.left U :=
  EtaleSeparatedFiniteType.zeroSieve_mem_of_generic_open_zeros
    (integralAffineLocalZero_of_field k) _
    (withParameter_isA1Invariant _ hP (SmoothSite.multiplicativeGroupObject (Spec (.of k))))
    (hasGenericOpenZeros_of_affineLocalizationZero _ (torus_affineLocalizationZero_succ F n hP))
    X U s

/-- The ordinary small-site sheafification of the original positive torus
cohomology presheaf is zero. -/
theorem isZero_smallSheafify_torus_succ
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (hP : (withTransfers k F (n + 1)).IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    IsZero ((presheafToSheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left)
      AddCommGrpCat.{u + 1}).obj
      ((EtaleSeparatedFiniteType.toSmoothSite X).op ⋙ (toPresheaf k).obj
        (torusSections (withTransfers k F (n + 1))))) :=
  Presheaf.isZero_sheafify_of_locally_zero _ _ (torus_zeroSieve_mem_succ F n hP X)

end AlgebraicGeometry.SheafCohomology
