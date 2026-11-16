/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeDoubleContractionSwap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatProjectionUnitNaturality
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula

/-!
# The double Laurent unit and its two-chart quotient

The actual two scalar-unit operations descend to the double Bass quotient, where
the induced Laurent swap acts on the image by negation.

Sources: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/NativeDoubleForwardQuotient.lean`,
`ProductUnitInterchangeSign.lean`, and `CoefficientBassSplitMaps.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open KTheory.Bass.TwoChart AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules.ProductUnitInterchange
universe u
namespace AlgebraicGeometry.Scheme.Modules.CoefficientDoubleNativeUnit
attribute [local instance] CategoryTheory.Waldhausen.Additivity.KCommGroup
local notation "p" => NatTrans.op PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op PolynomialLaurent.Relative.minus
local notation "L" => PolynomialLaurent.Relative.laurentFunctor.op
local notation "ℓ" => PolynomialLaurent.laurentProjection
  (CommRingCat.of (ULift ℤ))
local notation "t" => PolynomialLaurent.laurentCoordinate
  (CommRingCat.of (ULift ℤ))
local notation "ℒ" => baseProductFunctor ℓ

/-- The unchanged flat K-groups and pullbacks, in additive notation. -/
def boundedAboveFlatPerfectKAddFunctor (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj X := AddCommGrpCat.of (Additive (boundedAboveFlatPerfectK X.unop.toRingedSpace n))
  map f := AddCommGrpCat.ofHom (boundedAboveFlatPerfectKPullback f.unop n).toAdditive
  map_id X := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (boundedAboveFlatPerfectKPullback_id X.unop n)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive
      (boundedAboveFlatPerfectKPullback_comp g.unop f.unop n)

/-- The literal double Laurent operation before quotienting. -/
def doubleLaurentUnitMap (X : Scheme.{u}) :
    (boundedAboveFlatPerfectKAddFunctor 0).obj (Opposite.op X) ⟶
      (boundedAboveFlatPerfectKAddFunctor 2).obj (Opposite.op ((ℒ).obj ((ℒ).obj X))) :=
  AddCommGrpCat.ofHom (doubleProjectionUnitOperation ℓ ℓ X t t 0).toAdditive

/-- Actual geometric factor interchange is minus the unchanged original double unit arrow. -/
theorem doubleLaurentUnitMap_swap (X : Scheme.{u}) :
    doubleLaurentUnitMap X ≫ (boundedAboveFlatPerfectKAddFunctor 2).map
      (baseProductSwapMap ℓ ℓ X).op = -doubleLaurentUnitMap X := by
  ext a
  exact congrArg Additive.ofMul
    (doubleLaurentProjectionUnit_KZero_swap X (Additive.toMul a))

private theorem additiveOfHom_comp {A B C : Type (u + 1)}
    [CommGroup A] [CommGroup B] [CommGroup C] (f : A →* B) (g : B →* C) :
    (AddCommGrpCat.ofHom f.toAdditive :
      AddCommGrpCat.of (Additive A) ⟶ AddCommGrpCat.of (Additive B)) ≫
      AddCommGrpCat.ofHom g.toAdditive = AddCommGrpCat.ofHom (g.comp f).toAdditive := rfl

/-- The unchanged original K-functor restricted to the actual quasi-compact schemes. -/
def quasiCompactKFunctor (n : ℕ) : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  quasiCompactSchemesInclusion.op ⋙ boundedAboveFlatPerfectKAddFunctor n

/-- Naturality of the unchanged original double unit as an additive arrow on schemes. -/
theorem doubleLaurentUnitMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectKAddFunctor 0).map f.op ≫ doubleLaurentUnitMap X =
      doubleLaurentUnitMap Y ≫
        (boundedAboveFlatPerfectKAddFunctor 2).map ((ℒ).map ((ℒ).map f)).op := by
  dsimp only [doubleLaurentUnitMap, boundedAboveFlatPerfectKAddFunctor]
  rw [additiveOfHom_comp, additiveOfHom_comp]
  simp only [Quiver.Hom.unop_op]
  erw [doubleUnit_naturality ℓ ℓ f t t 0]

/-- The literal native K-zero to double-Laurent K-two operation on the all-qc domain. -/
def doubleUnitSection : quasiCompactKFunctor.{u} 0 ⟶ L ⋙ L ⋙ quasiCompactKFunctor 2 where
  app X := doubleLaurentUnitMap X.unop.obj
  naturality {X Y} f := by
    change (boundedAboveFlatPerfectKAddFunctor 0).map f.unop.hom.op ≫
        doubleLaurentUnitMap Y.unop.obj =
      doubleLaurentUnitMap X.unop.obj ≫
        (boundedAboveFlatPerfectKAddFunctor 2).map ((ℒ).map ((ℒ).map f.unop.hom)).op
    exact doubleLaurentUnitMap_naturality f.unop.hom

/-- The native twice-positive comparison uses the two unchanged original projections. -/
def doubleForwardQuotient :
    quasiCompactKFunctor.{u} 0 ⟶ contraction p m (contraction p m (quasiCompactKFunctor 2)) :=
  doubleUnitSection ≫
    { app X := doubleContractionπ p m (quasiCompactKFunctor 2) X
      naturality {_ _} f := doubleContractionπ_naturality p m (quasiCompactKFunctor 2) f }

/-- The actual native comparison intertwines the descended swap with its proved unit sign. -/
theorem doubleForwardQuotient_swap (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    doubleForwardQuotient.app X ≫
        PolynomialLaurent.Relative.doubleContractionSwap (quasiCompactKFunctor 2) X =
      -doubleForwardQuotient.app X := by
  change (doubleLaurentUnitMap X.unop.obj ≫ _) ≫ _ = -(_ ≫ _)
  rw [Category.assoc, PolynomialLaurent.Relative.doubleContractionπ_swap,
    ← Category.assoc]
  change (doubleLaurentUnitMap X.unop.obj ≫ (boundedAboveFlatPerfectKAddFunctor 2).map
    (baseProductSwapMap ℓ ℓ X.unop.obj).op) ≫ _ = _
  rw [doubleLaurentUnitMap_swap, Preadditive.neg_comp]
  rfl

end AlgebraicGeometry.Scheme.Modules.CoefficientDoubleNativeUnit
