/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.UnitPoints
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Hypercohomology
public import Colib.CategoryTheory.Sites.RelativeCohomology.ExactSequence

/-!
# The relative weight-one class of the torus coordinate

The forward Laurent coordinate on the native torus restricts to the unit one
along its identity section. The corresponding map of free representing sheaves
therefore factors through the relative source of that section. The geometric
weight-one comparison carries its degree-zero units class to bidegree (1,1).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers
open Stacks.Cohomology.FreeYonedaUnivLE

universe d w u

namespace AlgebraicGeometry.MotivicHomotopy

open AlgebraicGeometry.MotivicCohomology.WeightOne

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "Uₖ" => largeUnitsSheaf Sₖ

/-- The forward Laurent coordinate in the ordinary large Nisnevich units sheaf. -/
def torusCoordinateUnitSection : (Uₖ).obj.obj (op Gₖ) :=
  ULift.up (Additive.ofMul (multiplicativeGroupBaseChangeCoordinate Sₖ))

/-- The actual restriction to the torus identity is zero in additive notation. -/
theorem torusOne_pullback_coordinateUnit :
    (Uₖ).obj.map (torusOne Sₖ).op (torusCoordinateUnitSection k) = 0 := by
  have h : Units.map (torusOne Sₖ).left.appTop.hom.toMonoidHom
      (multiplicativeGroupBaseChangeCoordinate Sₖ) = (1 : (Γ(Sₖ, ⊤))ˣ) :=
    nativeTorusPoint_coordinate (𝟙 Sₖ) 1
  exact (largeUnitsPresheaf_map_apply (torusOne Sₖ)
    (multiplicativeGroupBaseChangeCoordinate Sₖ)).trans
      (congrArg (fun v => ULift.up (Additive.ofMul v)) h)

private def torusCoordinateHom : (freeYoneda.{u + 1} Jₖ).obj Gₖ ⟶ Uₖ :=
  (sectionsAddEquiv.{u + 1} Gₖ Uₖ).symm (torusCoordinateUnitSection k)

private theorem torusOne_torusCoordinateHom :
    (freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ) ≫ torusCoordinateHom k = 0 := by
  apply (sectionsAddEquiv.{u + 1} (base Sₖ) Uₖ).injective
  rw [map_zero, sectionsAddEquiv_apply, sectionsEquiv_naturality_left]
  change (Uₖ).obj.map (torusOne Sₖ).op
    (sectionsAddEquiv.{u + 1} Gₖ Uₖ (torusCoordinateHom k)) = 0
  rw [torusCoordinateHom, AddEquiv.apply_symm_apply]
  exact torusOne_pullback_coordinateUnit k

/-- The relative sheaf morphism determined by the literal coordinate and identity. -/
@[no_expose]
def torusCoordinateRelativeUnit : relativeSource.{u + 1} Jₖ (torusOne Sₖ) ⟶ Uₖ :=
  cokernel.desc ((freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ)) (torusCoordinateHom k)
    (torusOne_torusCoordinateHom k)

/-- The actual quotient leg recovers the forward coordinate under free-Yoneda evaluation. -/
theorem sectionsAddEquiv_relativeSourceπ_torusCoordinateRelativeUnit :
    sectionsAddEquiv.{u + 1} Gₖ Uₖ
      (relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ) ≫ torusCoordinateRelativeUnit k) =
        torusCoordinateUnitSection k := by
  have h : relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ) ≫ torusCoordinateRelativeUnit k =
      torusCoordinateHom k :=
    cokernel.π_desc ((freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ)) _ _
  rw [h]
  exact (sectionsAddEquiv.{u + 1} Gₖ Uₖ).apply_symm_apply _

section Ext

variable [HasExt.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The coordinate gives the ordinary relative degree-zero class of the units sheaf. -/
def torusCoordinateRelativeExt : relativeH.{w, u + 1} Jₖ (torusOne Sₖ) Uₖ 0 :=
  Ext.mk₀.{w} (torusCoordinateRelativeUnit k)

/-- Forgetting relativity and evaluating degree-zero Ext recovers the original unit. -/
theorem extSectionsAddEquiv_relativeForget_torusCoordinateRelativeExt :
    extSectionsAddEquiv.{w, u + 1} Gₖ Uₖ
      (relativeForget.{w, u + 1} Jₖ (torusOne Sₖ) Uₖ 0
        (torusCoordinateRelativeExt.{w} k)) =
        torusCoordinateUnitSection k := by
  rw [relativeForget_apply.{w, u + 1}]
  let π := relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ)
  let t : Ext.{w} (relativeSource.{u + 1} Jₖ (torusOne Sₖ)) Uₖ 0 :=
    torusCoordinateRelativeExt.{w} k
  let e := sectionsAddEquiv.{u + 1} Gₖ Uₖ
  have ht : Ext.addEquiv₀.{w} t = torusCoordinateRelativeUnit k :=
    Ext.addEquiv₀.{w}.apply_symm_apply _
  change e (Ext.addEquiv₀.{w} ((Ext.mk₀.{w} π).comp t (zero_add 0))) = _
  calc
    _ = e (π ≫ Ext.addEquiv₀.{w} t) :=
      congrArg e (addEquiv₀_mk₀_comp.{w, u + 1} (J := Jₖ) π t)
    _ = e (π ≫ torusCoordinateRelativeUnit k) := congrArg (fun f => e (π ≫ f)) ht
    _ = _ := sectionsAddEquiv_relativeSourceπ_torusCoordinateRelativeUnit k

end Ext

section Derived

variable [HasDerivedCategory.{d}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The geometric weight-one comparison in cohomological degree one, with its signed shift. -/
def weightOneDerivedUnitsIso :
    (DerivedCategory.Q.{d}.obj (motivicSheafComplex k 1))⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).obj Uₖ :=
  let K := (CochainComplex.singleFunctor (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).obj Uₖ
  let e := asIso (DerivedCategory.Q.{d}.map (weightOneSheafComparison k))
  (shiftFunctor _ (1 : ℤ)).mapIso e ≪≫
    hypercohomologyShiftTargetIso.{d, u + 1} Jₖ K (-1) 1 ≪≫
    (shiftFunctorZero (DerivedCategory.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1})) ℤ).app
      (DerivedCategory.Q.{d}.obj K) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ.{d}
      (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).app Uₖ).symm

/-- The relative motivic class represented by the coordinate unit in bidegree (1,1). -/
@[colib_tag "COL-1034", colib_ref "Voevodsky2003ReducedPowers"
  "Section 2, before (2.8) and equation (2.9), p. 5"
  "ingredient" "The forward torus coordinate as the relative input to the Tate suspension class"]
def torusCoordinateRelativeMotivicClass :
    (DerivedCategory.singleFunctor.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).obj
        (relativeSource.{u + 1} Jₖ (torusOne Sₖ)) ⟶
      (DerivedCategory.Q.{d}.obj (motivicSheafComplex k 1))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.singleFunctor.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).map
      (torusCoordinateRelativeUnit k) ≫ (weightOneDerivedUnitsIso.{d} k).inv

/-- The specified signed comparison recovers the actual relative units map. -/
@[colib_tag "COL-1034", reassoc]
theorem torusCoordinateRelativeMotivicClass_comp_weightOneDerivedUnitsIso :
    torusCoordinateRelativeMotivicClass.{d} k ≫ (weightOneDerivedUnitsIso.{d} k).hom =
      (DerivedCategory.singleFunctor.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).map
        (torusCoordinateRelativeUnit k) := by
  rw [torusCoordinateRelativeMotivicClass, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Derived

end AlgebraicGeometry.MotivicHomotopy
