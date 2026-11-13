/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Cofiber
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.CoordinateReduced
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Functor

/-!
# The coordinate class on the Tate quotient

The connecting map of the reduced-cochain sequence for the actual Laurent
open carries the pointed torus coordinate to bidegree (2,1) on the Tate
quotient. The class uses the connecting morphism of the existing derived
triangle and the native addition isomorphism for shifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]
  [HasDerivedCategory.{d}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Rₖ" => CommRingCat.of k
local notation "Sₖ" => Spec Rₖ
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ

/-- The connecting image of the forward torus coordinate in bidegree (2,1). -/
@[no_expose, colib_tag "COL-1036", colib_ref "Voevodsky2003ReducedPowers"
  "Section 2, pp. 5–6, following (2.9)"
  "ingredient" "The reduced torus coordinate transported to the Tate quotient"]
def tateCoordinateClass :
    (reducedHypercohomology.{d, u + 1} Cₖ Jₖ (motivicSheafComplex k 1) 2).obj
      (op (liftedTateSphere Rₖ)) :=
  let D := DerivedCategory.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1})
  let K := DerivedCategory.Q.{d}.obj (motivicSheafComplex k 1)
  tateSphereConnecting.{d} Rₖ ≫ (torusCoordinateReducedMotivicClass.{d} k)⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd D (1 : ℤ) 1).inv.app K

/-- The degree-two weight-one comparison has target the units sheaf shifted once. -/
def weightOneTateDerivedUnitsIso :
    (DerivedCategory.Q.{d}.obj (motivicSheafComplex k 1))⟦(2 : ℤ)⟧ ≅
      ((DerivedCategory.singleFunctor.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).obj
        (largeUnitsSheaf Sₖ))⟦(1 : ℤ)⟧ :=
  let D := DerivedCategory.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1})
  let K := DerivedCategory.Q.{d}.obj (motivicSheafComplex k 1)
  (shiftFunctorAdd D (1 : ℤ) 1).app K ≪≫
    (shiftFunctor D (1 : ℤ)).mapIso (weightOneDerivedUnitsIso.{d} k)

/-- Under the signed weight-one comparison, the class is the connecting image
of the same relative units map. -/
@[colib_tag "COL-1036", reassoc]
theorem tateCoordinateClass_comp_weightOneTateDerivedUnitsIso :
    tateCoordinateClass.{d} k ≫ (weightOneTateDerivedUnitsIso.{d} k).hom =
      tateSphereConnecting.{d} Rₖ ≫
        ((torusReducedDerivedChainsIso.{d} k).hom ≫
          (DerivedCategory.singleFunctor.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).map
            (torusCoordinateRelativeUnit k))⟦(1 : ℤ)⟧' := by
  let D := DerivedCategory.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1})
  let K := DerivedCategory.Q.{d}.obj (motivicSheafComplex k 1)
  let S := shiftFunctor D (1 : ℤ)
  let e := (shiftFunctorAdd D (1 : ℤ) 1).app K
  let δ := tateSphereConnecting.{d} Rₖ
  let x := torusCoordinateReducedMotivicClass.{d} k
  let ν := (weightOneDerivedUnitsIso.{d} k).hom
  change (δ ≫ S.map x ≫ e.inv) ≫ (e.hom ≫ S.map ν) = _
  calc
    _ = δ ≫ S.map x ≫ S.map ν := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = δ ≫ S.map (x ≫ ν) := congrArg (fun f => δ ≫ f) (S.map_comp x ν).symm
    _ = _ := congrArg (fun f => δ ≫ S.map f)
      (torusCoordinateReducedMotivicClass_comp_weightOneDerivedUnitsIso.{d} k)

end AlgebraicGeometry.MotivicHomotopy
