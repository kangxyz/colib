/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectGlobalUnit

/-! # The original global-unit automorphism of geometric bounded-flat pullback -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The unit acts on the actual target complex of geometric pullback. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/GlobalUnit.lean:32-37"
  "adaptation" "The original unit automorphism on arbitrary geometric bounded-flat pullback"]
def boundedAboveFlatPerfectPullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) : boundedAboveFlatPerfectPullback f ≅ boundedAboveFlatPerfectPullback f :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (boundedAboveFlatPerfectPullback f)
      (boundedAboveFlatPerfectGlobalUnitIso X r) ≪≫ Functor.rightUnitor _

end AlgebraicGeometry.Scheme.Modules
