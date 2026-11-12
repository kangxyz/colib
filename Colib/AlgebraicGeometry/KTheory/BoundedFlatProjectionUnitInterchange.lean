/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalUnitFactor
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProductInterchange

/-!
# Actual projection-unit interchange on bounded-flat K-theory

Two actual product projections and their scalar units give the raw double operation.
The genuine factor swap negates it in every nonnegative degree, before quotienting.
This does not assert invertibility of the positive Bass comparison or a negative quotient sign.

Source: Quillen `ProductSwapUnit`, `ProductSwapOuterUnit`, `ProductUnitInterchangeSign`
at revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Products CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules
namespace ProductSwapUnit
variable {S T : Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
  (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
  (X : Scheme.{u})

/-- Projection to S in the unswapped product (X × S) × T. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapUnit.lean:42"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
def innerProjection : (baseProductFunctor q).obj ((baseProductFunctor p).obj X) ⟶ S :=
  pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q ≫
    pullback.snd (specULiftZIsTerminal.from X) p

/-- Projection to S in the swapped product (X × T) × S. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapUnit.lean:47"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
def outerProjection : (baseProductFunctor p).obj ((baseProductFunctor q).obj X) ⟶ S :=
  pullback.snd (specULiftZIsTerminal.from ((baseProductFunctor q).obj X)) p

/-- The original first-factor unit on the unswapped product. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapUnit.lean:51"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
def innerUnit (r : Γ(S, ⊤)ˣ) :
    Γ((baseProductFunctor q).obj ((baseProductFunctor p).obj X), ⊤)ˣ :=
  Units.map (innerProjection p q X).appTop.hom.toMonoidHom r

/-- The same factor's unit on the swapped product. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapUnit.lean:56"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
def outerUnit (r : Γ(S, ⊤)ˣ) :
    Γ((baseProductFunctor p).obj ((baseProductFunctor q).obj X), ⊤)ˣ :=
  Units.map (outerProjection p q X).appTop.hom.toMonoidHom r

/-- Pulling back the outer S-unit along the actual swap recovers the inner S-unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapUnit.lean:61"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
theorem swap_unit (r : Γ(S, ⊤)ˣ) :
    Units.map (baseProductSwapMap p q X).appTop.hom.toMonoidHom
      (outerUnit p q X r) = innerUnit p q X r := by
  apply Units.ext
  have h := congrArg (fun f => f.appTop) (baseProductSwapMap_snd p q X)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)


end ProductSwapUnit
namespace ProductSwapOuterUnit
open ProductSwapUnit
variable {S T : Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
  (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u})
/-- The new direction uses the literal inverse of the previously checked swap. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapOuterUnit.lean:36"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
theorem swap_is_original_inverse :
    baseProductSwapMap p q X = (baseProductSwapIso q p).inv.app X := rfl

/-- Pullback along σ(S,T) sends the inner T-unit to the original outer T-unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapOuterUnit.lean:40"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
theorem swap_outer_unit (r : Γ(T, ⊤)ˣ) :
    Units.map (baseProductSwapMap p q X).appTop.hom.toMonoidHom
      (innerUnit q p X r) = outerUnit q p X r := by
  apply Units.ext
  have h := congrArg (fun f => f.appTop) (baseProductSwapMap_fst_snd p q X)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)


end ProductSwapOuterUnit
namespace ProductUnitInterchange
open ProductSwapUnit GlobalUnitIdentityOperation
variable {S T : Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
  (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))

/-- The actual factor unit pulled back to the original one-factor product. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductUnitInterchangeSign.lean:45"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
def projectionUnit (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ) :
    (Γ((baseProductFunctor p).obj X, ⊤))ˣ :=
  Units.map (pullback.snd (specULiftZIsTerminal.from X) p).appTop.hom.toMonoidHom r

/-- The original raw projection-unit operation, with its complete chosen-zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductUnitInterchangeSign.lean:50"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
def projectionUnitOperation (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ) (n : ℕ) :
    boundedAboveFlatPerfectK X.toRingedSpace n →*
      boundedAboveFlatPerfectK ((baseProductFunctor p).obj X).toRingedSpace (n + 1) :=
  originalKSelfTrackOperation (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen ((baseProductFunctor p).obj X).toRingedSpace)
    (boundedAboveFlatPerfectUnitHomotopy ((baseProductProjection p).app X)
      (projectionUnit p X r)) n

/-- The two original projections and units, in their specified order. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductUnitInterchangeSign.lean:58"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
def doubleProjectionUnitOperation (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ)
    (s : (Γ(T, ⊤))ˣ) (n : ℕ) :
    boundedAboveFlatPerfectK X.toRingedSpace n →*
      boundedAboveFlatPerfectK ((baseProductFunctor q).obj
        ((baseProductFunctor p).obj X)).toRingedSpace (n + 2) :=
  (projectionUnitOperation q ((baseProductFunctor p).obj X) s (n + 1)).comp
    (projectionUnitOperation p X r n)

/-- Pullback along the second original projection is precisely the first-factor unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductUnitInterchangeSign.lean:66"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
theorem projectionUnit_pullback (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ) :
    Units.map ((baseProductProjection q).app ((baseProductFunctor p).obj X)).appTop.hom.toMonoidHom
      (projectionUnit p X r) = innerUnit p q X r := by
  apply Units.ext
  change (((baseProductProjection q).app ((baseProductFunctor p).obj X)).appTop.hom
    ((pullback.snd (specULiftZIsTerminal.from X) p).appTop.hom (↑r))) =
      (innerProjection p q X).appTop.hom (↑r)
  rw [innerProjection, Scheme.Hom.comp_appTop]
  rfl

set_option maxHeartbeats 800000 in
-- Retain the actual nested flat-complex maps while elaborating their factorization.
set_option backward.isDefEq.respectTransparency.types false in
/-- Both raw operations retain the actual target identity actions and original base pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductUnitInterchangeSign.lean:78"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
theorem doubleProjectionUnitOperation_factor (X : Scheme.{u})
    (r : (Γ(S, ⊤))ˣ) (s : (Γ(T, ⊤))ˣ) (n : ℕ) (a : boundedAboveFlatPerfectK X.toRingedSpace n) :
    doubleProjectionUnitOperation p q X r s n a =
      unitKOperation _ (outerUnit q p X s) (n + 1)
        (unitKOperation _ (innerUnit p q X r) n
          (boundedAboveFlatPerfectKPullback
            (((baseProductProjection q).app ((baseProductFunctor p).obj X)) ≫
              (baseProductProjection p).app X) n a)) := by
  simp only [doubleProjectionUnitOperation, projectionUnitOperation,
    originalUnit_operation, MonoidHom.comp_apply]
  have h := DFunLike.congr_fun
    (unitKOperation_pullback ((baseProductProjection q).app ((baseProductFunctor p).obj X))
      (projectionUnit p X r) n)
    (boundedAboveFlatPerfectKPullback ((baseProductProjection p).app X) n a)
  change boundedAboveFlatPerfectKPullback
      ((baseProductProjection q).app ((baseProductFunctor p).obj X)) (n + 1)
      (unitKOperation _ (projectionUnit p X r) n
        (boundedAboveFlatPerfectKPullback ((baseProductProjection p).app X) n a)) =
    unitKOperation _
      (Units.map ((baseProductProjection q).app
        ((baseProductFunctor p).obj X)).appTop.hom.toMonoidHom (projectionUnit p X r)) n
      (boundedAboveFlatPerfectKPullback ((baseProductProjection q).app
        ((baseProductFunctor p).obj X)) n
        (boundedAboveFlatPerfectKPullback ((baseProductProjection p).app X) n a)) at h
  rw [projectionUnit_pullback] at h
  have hp := DFunLike.congr_fun
    (boundedAboveFlatPerfectKPullback_comp
      ((baseProductProjection q).app ((baseProductFunctor p).obj X))
      ((baseProductProjection p).app X) n) a
  have hi := congrArg
    (unitKOperation ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))
      (innerUnit p q X r) n) hp.symm
  exact congrArg
    (unitKOperation ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))
      (outerUnit q p X s) (n + 1)) (h.trans hi)

set_option maxHeartbeats 800000 in
-- Elaborating the native nested flat-complex pullbacks needs a larger reduction budget.
/-- The actual geometric swap reverses the two original projection-unit operations. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductUnitInterchangeSign.lean:115"
  "adaptation" "Actual product projections, pulled-back units and original K-operations."]
theorem doubleProjectionUnitOperation_swap (X : Scheme.{u})
    (r : (Γ(S, ⊤))ˣ) (s : (Γ(T, ⊤))ˣ) (n : ℕ) (a : boundedAboveFlatPerfectK X.toRingedSpace n) :
    boundedAboveFlatPerfectKPullback (baseProductSwapMap p q X) (n + 2)
      (doubleProjectionUnitOperation q p X s r n a) =
        (doubleProjectionUnitOperation p q X r s n a)⁻¹ := by
  rw [doubleProjectionUnitOperation_factor, doubleProjectionUnitOperation_factor]
  have h₁ := DFunLike.congr_fun
    (unitKOperation_pullback (baseProductSwapMap p q X) (outerUnit p q X r) (n + 1))
    (unitKOperation _ (innerUnit q p X s) n
      (boundedAboveFlatPerfectKPullback
        (((baseProductProjection p).app ((baseProductFunctor q).obj X)) ≫
          (baseProductProjection q).app X) n a))
  simp only [MonoidHom.comp_apply, swap_unit] at h₁
  rw [h₁]
  have h₂ := DFunLike.congr_fun
    (unitKOperation_pullback (baseProductSwapMap p q X) (innerUnit q p X s) n)
    (boundedAboveFlatPerfectKPullback
      (((baseProductProjection p).app ((baseProductFunctor q).obj X)) ≫
        (baseProductProjection q).app X) n a)
  simp only [MonoidHom.comp_apply, ProductSwapOuterUnit.swap_outer_unit] at h₂
  rw [h₂]
  have hb : baseProductSwapMap p q X ≫
      ((baseProductProjection p).app ((baseProductFunctor q).obj X)) ≫
        (baseProductProjection q).app X =
      ((baseProductProjection q).app ((baseProductFunctor p).obj X)) ≫
        (baseProductProjection p).app X := baseProductSwapMap_fst_fst p q X
  have hbK : boundedAboveFlatPerfectKPullback (baseProductSwapMap p q X) n
      (boundedAboveFlatPerfectKPullback
        (((baseProductProjection p).app ((baseProductFunctor q).obj X)) ≫
          (baseProductProjection q).app X) n a) =
      boundedAboveFlatPerfectKPullback
        (((baseProductProjection q).app ((baseProductFunctor p).obj X)) ≫
          (baseProductProjection p).app X) n a := by
    rw [← MonoidHom.comp_apply, ← boundedAboveFlatPerfectKPullback_comp, hb]
  rw [hbK]
  exact unitKOperation_interchange_sign _ (outerUnit q p X s) (innerUnit p q X r) n _


end ProductUnitInterchange
end AlgebraicGeometry.Scheme.Modules
