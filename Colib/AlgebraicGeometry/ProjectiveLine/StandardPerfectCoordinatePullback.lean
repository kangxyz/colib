/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinatePullbackIso
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardPerfectCoordinate
public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullbackRestriction
public import Colib.AlgebraicGeometry.Modules.PerfectOpenWeak

/-! # The chart frame for native perfect complexes -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

set_option backward.isDefEq.respectTransparency false in
/-- After pulling back to the corresponding standard chart, the actual coordinate map
on a perfect complex is a degreewise isomorphism. -/
theorem isIso_pullback_perfectNegativeTwistCoordinate (S : Scheme.{u}) (i : Fin 2)
    (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (projectiveSpaceOver 1 S).toRingedSpace))) :
    IsIso (((Modules.perfectFlatPullback (standardChart S i).ι).map
      ((perfectNegativeTwistCoordinate S i).app K)).hom) := by
  let : ∀ j, IsIso (((Modules.perfectFlatPullback (standardChart S i).ι).map
      ((perfectNegativeTwistCoordinate S i).app K)).hom.f j) := fun j =>
    isIso_pullback_negativeTwistCoordinate S i (K.obj.X j)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The actual coordinate map is an isomorphism after restricting to its own chart. -/
theorem isIso_restrict_perfectNegativeTwistCoordinate (S : Scheme.{u}) (i : Fin 2)
    (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (projectiveSpaceOver 1 S).toRingedSpace))) :
    IsIso ((Modules.perfectComplexesRestrictOpenImmersion (standardChart S i).ι).map
      ((perfectNegativeTwistCoordinate S i).app K)) := by
  let α := (perfectNegativeTwistCoordinate S i).app K
  let j := (standardChart S i).ι
  let I := ObjectProperty.ι
    (RingedSpace.IsPerfectComplex (X := (standardChart S i).toScheme.toRingedSpace))
  let p := (Modules.perfectFlatPullback j).map α
  let : IsIso (I.map p) := isIso_pullback_perfectNegativeTwistCoordinate S i K
  let : IsIso p := isIso_of_reflects_iso p I
  exact (NatIso.isIso_map_iff (Modules.perfectRestrictIsoFlatPullback j) α).2
    (inferInstanceAs (IsIso p))

/-- The actual coordinate map is weak on the chart it defines, in the unchanged
relative Waldhausen structure. -/
theorem perfectNegativeTwistCoordinate_openWeak (S : Scheme.{u}) (i : Fin 2)
    (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (projectiveSpaceOver 1 S).toRingedSpace))) :
    (Modules.perfectOpenWeakWaldhausen (standardChart S i).ι).weq
      ((perfectNegativeTwistCoordinate S i).app K) := by
  let α := (perfectNegativeTwistCoordinate S i).app K
  let j := (standardChart S i).ι
  let : IsIso ((Modules.perfectComplexesRestrictOpenImmersion j).map α) :=
    isIso_restrict_perfectNegativeTwistCoordinate S i K
  exact (Modules.perfectOpenWeakWaldhausen_weq_iff j α).2 (by
    change QuasiIso ((Modules.perfectComplexesRestrictOpenImmersion j).map α).hom
    infer_instance)

end AlgebraicGeometry.Scheme.ProjectiveLine
