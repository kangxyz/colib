/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Idempotents
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Tate
public import Colib.CategoryTheory.Triangulated.SignedShift
public import Colib.CategoryTheory.Triangulated.Stabilization.Additive
public import Colib.CategoryTheory.Triangulated.Stabilization.ExactInverse
public import Colib.CategoryTheory.Triangulated.Stabilization.Idempotents
public import Colib.CategoryTheory.Triangulated.Stabilization.Inverse
import Colib.Util.References

/-!
# Geometric motives after Tate inversion

The native cancellation theorem supplies the fully faithful transitions
between finite twist stages. The transition functor tensors with the
reduced torus and shifts by one, which gives the Lefschetz twist.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The exact Lefschetz twist on effective geometric motives. -/
abbrev geometricLefschetzTensor : EffectiveGeometricMotives k ⥤ EffectiveGeometricMotives k :=
  geometricReducedTorusTensor k ⋙ shiftFunctor (EffectiveGeometricMotives k) (1 : ℤ)

/-- Geometric motives with finite inverse Lefschetz twists. -/
@[colib_tag "COL-1224", colib_ref "Voevodsky2000TriangulatedMotives"
  "Section 2.1, after Proposition 2.1.3" "adaptation"
  "The triangulated stabilization along finite powers of the Lefschetz twist"]
abbrev GeometricMotives := Stabilization (geometricLefschetzTensor k)

/-- The original effective geometric category sits at twist stage zero. -/
abbrev geometricMotivesInclusion : EffectiveGeometricMotives k ⥤ GeometricMotives k :=
  Stabilization.inclusion (geometricLefschetzTensor k)

/-- The motive of a smooth scheme or finite correspondence after stabilization. -/
def geometricMotive : Cor k ⥤ GeometricMotives k :=
  effectiveGeometricMotive k ⋙ geometricMotivesInclusion k

/-- The Lefschetz twist becomes an autoequivalence. -/
abbrev geometricLefschetzTwist : GeometricMotives k ≌ GeometricMotives k :=
  Stabilization.twistEquivalence (geometricLefschetzTensor k)

/-- The stable Lefschetz twist restricts to the original exact effective twist. -/
def geometricLefschetzTwistInclusionIso :
    geometricMotivesInclusion k ⋙ (geometricLefschetzTwist k).functor ≅
      geometricLefschetzTensor k ⋙ geometricMotivesInclusion k :=
  Stabilization.twistInclusionIso (geometricLefschetzTensor k)

end AlgebraicGeometry.MotivicHomotopy
