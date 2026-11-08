module

import Colib.AlgebraicGeometry.GroupScheme.LaurentOpen
import Colib.AlgebraicGeometry.Modules.PerfectRankOneRestriction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

example (X : Scheme.{u}) (n : ℤ) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
      ((CochainComplex.singleFunctor X.Modules n).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
  Scheme.Modules.Complex.isPerfectComplex_single_unit X n

example (X : Scheme.{u}) :
    (Scheme.Modules.rankOnePerfectComplex X).obj =
      (CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) := rfl

example {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    (Scheme.Modules.perfectComplexesRestrictOpenImmersion j).obj
        (Scheme.Modules.rankOnePerfectComplex X) ≅ Scheme.Modules.rankOnePerfectComplex Y :=
  Scheme.Modules.rankOnePerfectComplexRestrictIso j

example : multiplicativeGroupToAdditive.{u} =
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := ULift.{u} ℤ))) := rfl

example : IsOpenImmersion multiplicativeGroupToAdditive.{u} := inferInstance

example : multiplicativeGroupToAdditive.{u}.appTop additiveCoordinate =
    (multiplicativeCoordinate : (Γ(multiplicativeGroupULift.{u}, ⊤))ˣ).val :=
  multiplicativeGroupToAdditive_appTop_coordinate

example (X : Scheme.{u}) : IsOpenImmersion (multiplicativeGroupBaseChangeToAdditive X) :=
  inferInstance

example (X : Scheme.{u}) :
    (multiplicativeGroupBaseChangeToAdditive X).appTop
        (additiveGroupBaseChangeCoordinate X) =
      (multiplicativeGroupBaseChangeCoordinate X).val :=
  multiplicativeGroupBaseChangeToAdditive_appTop_coordinate X

end
