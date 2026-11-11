module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ChangeOfTopology
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LeftExact

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

universe u v w
noncomputable section

variable (S : Scheme.{u}) (A : Type v) [Category.{w} A]

example [HasWeakSheafify (etaleTopology S) A] :
    nisnevichToEtaleSheaf S A ⊣ etaleToNisnevichSheaf S A :=
  nisnevichToEtaleSheafAdjunction S A

example [HasWeakSheafify (etaleTopology S) A]
    (F : Sheaf (nisnevichTopology S) A) :
    ((nisnevichToEtaleSheafAdjunction S A).unit.app F).hom =
      toSheafify (etaleTopology S) F.obj :=
  nisnevichToEtaleSheafAdjunction_unit_app_hom S A F

example [HasWeakSheafify (etaleTopology S) A]
    (F : Sheaf (etaleTopology S) A) :
    ((nisnevichToEtaleSheafAdjunction S A).counit.app F).hom =
      sheafifyLift (etaleTopology S) (𝟙 F.obj) F.property :=
  nisnevichToEtaleSheafAdjunction_counit_app_hom S A F

example [HasWeakSheafify (etaleTopology S) A]
    (F : Sheaf (etaleTopology S) A) :
    IsIso ((nisnevichToEtaleSheafAdjunction S A).counit.app F) := inferInstance

example [HasWeakSheafify (etaleTopology S) A] :
    PreservesFiniteColimits (nisnevichToEtaleSheaf S A) := inferInstance

example [HasFiniteLimits A] [HasSheafify (etaleTopology S) A] :
    PreservesFiniteLimits (nisnevichToEtaleSheaf S A) := inferInstance

example [Abelian A] [HasSheafify (etaleTopology S) A] :
    (nisnevichToEtaleSheaf S A).Additive := inferInstance

section AbelianGroups

local instance : HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1} := by
  let : EssentiallySmall.{u + 1} (Scheme.SmoothSite S) := inferInstance
  exact hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1}
    (etaleTopology S) AddCommGrpCat.{u + 1}

example : nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1} ⊣
    etaleToNisnevichSheaf S AddCommGrpCat.{u + 1} :=
  nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1}

example : PreservesFiniteLimits (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}) :=
  inferInstance

example : PreservesFiniteColimits (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}) :=
  inferInstance

example : (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).Additive := inferInstance

end AbelianGroups
