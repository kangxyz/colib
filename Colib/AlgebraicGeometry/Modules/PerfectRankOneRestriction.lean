/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectRankOne
public import Colib.AlgebraicGeometry.Modules.PerfectOpenRestriction

/-!
# Restriction of the native rank-one perfect complex

The comparison is the actual single-complex restriction comparison followed by the native
structure-sheaf restriction isomorphism. Its underlying map is retained explicitly.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- The original degreewise open restriction of the structure single is the structure single. -/
def rankOnePerfectComplexRestrictIso :
    (perfectComplexesRestrictOpenImmersion j).obj (rankOnePerfectComplex X) ≅
      rankOnePerfectComplex Y :=
  ObjectProperty.isoMk (P := RingedSpace.IsPerfectComplex (X := Y.toRingedSpace))
    (((HomologicalComplex.singleMapHomologicalComplex
      (restrictFunctor j) (.up ℤ) 0).app (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      (CochainComplex.singleFunctor Y.Modules 0).mapIso (restrictUnitIso j))

/-- The inclusion into complexes retains the actual restriction comparison map. -/
@[simp]
theorem rankOnePerfectComplexRestrictIso_hom :
    (rankOnePerfectComplexRestrictIso j).hom.hom =
      ((HomologicalComplex.singleMapHomologicalComplex
        (restrictFunctor j) (.up ℤ) 0).app (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (CochainComplex.singleFunctor Y.Modules 0).map (restrictUnitIso j).hom := rfl

end AlgebraicGeometry.Scheme.Modules
