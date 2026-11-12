/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatProjectionUnitInterchange
public import Colib.AlgebraicGeometry.Scheme.LaurentCoordinateNaturality
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection

/-!
# Naturality and the actual double Laurent unit sign

Arbitrary scheme maps preserve the raw projection-unit operation, before either Bass
quotient. The double operation is the literal ordered composition of those operations.
The two original Laurent variables have the sign needed by the forward double quotient.
No invertibility of that quotient comparison is asserted here.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Products CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalUnitIdentityOperation
universe u
namespace AlgebraicGeometry.Scheme.Modules.ProductUnitInterchange
variable {S : Scheme.{u}} (p : S ⟶ Spec (.of (ULift.{u} ℤ)))

/-- Every base map preserves the same independent-factor unit on its product. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProjectionUnitNaturality.lean:28"
  "adaptation" "The actual pulled-back factor unit under every scheme map."]
theorem projectionUnit_map {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(S, ⊤))ˣ) :
    Units.map ((baseProductFunctor p).map f).appTop.hom.toMonoidHom
      (projectionUnit p Y r) = projectionUnit p X r := by
  apply Units.ext
  have h : (baseProductFunctor p).map f ≫ pullback.snd (specULiftZIsTerminal.from Y) p =
      pullback.snd (specULiftZIsTerminal.from X) p := by
    simp [baseProductFunctor]
  have hs := congrArg (fun g ↦ g.appTop) h
  rw [Scheme.Hom.comp_appTop] at hs
  exact ConcreteCategory.congr_hom hs (↑r)

/-- The original projection-unit operation is natural under every actual scheme morphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProjectionUnitNaturality.lean:40"
  "adaptation" "Original operation naturality via its proved actual identity-action factor."]
theorem projectionUnitOperation_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(S, ⊤))ˣ) (n : ℕ) :
    (boundedAboveFlatPerfectKPullback ((baseProductFunctor p).map f) (n + 1)).comp
        (projectionUnitOperation p Y r n) =
      (projectionUnitOperation p X r n).comp (boundedAboveFlatPerfectKPullback f n) := by
  simp only [projectionUnitOperation, originalUnit_operation]
  rw [← MonoidHom.comp_assoc, unitKOperation_pullback, projectionUnit_map,
    MonoidHom.comp_assoc, ← boundedAboveFlatPerfectKPullback_comp,
    MonoidHom.comp_assoc, ← boundedAboveFlatPerfectKPullback_comp,
    (baseProductProjection p).naturality f]
  rfl

/-- The two literal native projection-unit operations are natural before quotienting. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/NativeDoubleForwardQuotient.lean:53"
  "adaptation" "The same original two-operation proof for arbitrary fixed factors."]
theorem doubleUnit_naturality {T : Scheme.{u}} (q : T ⟶ Spec (.of (ULift.{u} ℤ)))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(S, ⊤))ˣ) (s : (Γ(T, ⊤))ˣ) (n : ℕ) :
    (boundedAboveFlatPerfectKPullback
        ((baseProductFunctor q).map ((baseProductFunctor p).map f)) (n + 2)).comp
        (doubleProjectionUnitOperation p q Y r s n) =
      (doubleProjectionUnitOperation p q X r s n).comp
        (boundedAboveFlatPerfectKPullback f n) := by
  unfold doubleProjectionUnitOperation
  rw [← MonoidHom.comp_assoc, projectionUnitOperation_naturality,
    MonoidHom.comp_assoc, projectionUnitOperation_naturality, ← MonoidHom.comp_assoc]

open AlgebraicGeometry.Scheme.PolynomialLaurent

set_option maxHeartbeats 800000 in
-- The actual two nested Laurent pullbacks require additional native-type elaboration.
/-- The literal double Laurent projection operation has its K-zero to K-two sign. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductUnitInterchangeSign.lean:153"
  "adaptation" "Actual original K-zero input, two forward Laurent units and geometric swap."]
theorem doubleLaurentProjectionUnit_KZero_swap (X : Scheme.{u})
    (a : boundedAboveFlatPerfectK X.toRingedSpace 0) :
    boundedAboveFlatPerfectKPullback
      (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X) 2
      (doubleProjectionUnitOperation (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X
        (laurentCoordinate (.of (ULift.{u} ℤ))) (laurentCoordinate (.of (ULift.{u} ℤ))) 0 a) =
    (doubleProjectionUnitOperation (laurentProjection (.of (ULift.{u} ℤ)))
      (laurentProjection (.of (ULift.{u} ℤ))) X
      (laurentCoordinate (.of (ULift.{u} ℤ))) (laurentCoordinate (.of (ULift.{u} ℤ))) 0 a)⁻¹ :=
  doubleProjectionUnitOperation_swap
    (laurentProjection (.of (ULift.{u} ℤ))) (laurentProjection (.of (ULift.{u} ℤ))) X
    (laurentCoordinate (.of (ULift.{u} ℤ))) (laurentCoordinate (.of (ULift.{u} ℤ))) 0 a

end AlgebraicGeometry.Scheme.Modules.ProductUnitInterchange
