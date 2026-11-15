/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductIdeal
public import Colib.RingTheory.Tor.ExteriorEuler.Quotient
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength

/-!
# The native closed product stalk as an exterior quotient

The two original stalk kernels generate the kernel of the product's closed
inclusion. Extending scalars from their exterior tensor therefore gives the
actual product stalk as a module over the ambient stalk.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-- The original closed-immersion stalk map at an explicitly identified ambient point. -/
abbrev transportedClosedStalkMap {T P : Scheme.{u}} (i : T ⟶ P) (z : T) (p : P)
    (hp : p = i z) : P.presheaf.stalk p →+* T.presheaf.stalk z :=
  ((P.presheaf.stalkCongr (.of_eq hp)).hom ≫ i.stalkMap z).hom

/-- The quotient presentation of the structure module of an actual closed-immersion stalk. -/
def quotientIsoClosedStalk {T P : Scheme.{u}} (i : T ⟶ P) [IsClosedImmersion i] (z : T) :
    ModuleCat.of (P.presheaf.stalk (i z))
      (P.presheaf.stalk (i z) ⧸ IdealSheafData.stalk i.ker (i z)) ≅
        (ModuleCat.restrictScalars (i.stalkMap z).hom).obj
          (ModuleCat.of (T.presheaf.stalk z) (T.presheaf.stalk z)) :=
  (Ideal.quotientEquivAlgOfEq (P.presheaf.stalk (i z))
    (ker_stalkMap_eq_idealStalk_ker i z).symm).toLinearEquiv.toModuleIso ≪≫
      Stacks.Intersection.Diagonal.kerQuotIso (i.stalkMap z).hom (i.stalkMap_surjective z)

/-- The quotient presentation at a named ambient point with its original stalk transport. -/
def quotientIsoTransportedClosedStalk {T P : Scheme.{u}} (i : T ⟶ P) [IsClosedImmersion i]
    (z : T) (p : P) (hp : p = i z) :
    ModuleCat.of (P.presheaf.stalk p)
      (P.presheaf.stalk p ⧸ IdealSheafData.stalk i.ker p) ≅
        (ModuleCat.restrictScalars (transportedClosedStalkMap i z p hp)).obj
          (ModuleCat.of (T.presheaf.stalk z) (T.presheaf.stalk z)) := by
  subst p
  simpa only [transportedClosedStalkMap, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] using quotientIsoClosedStalk i z

variable {S X Y A B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (i : A ⟶ X) (j : B ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
  (x : pullback (C := Scheme) f g)

/-- The transported product stalk has the actual scalar-extended exterior quotient module. -/
def exteriorQuotientsIsoTransportedClosedMapProductStalk
    {k : Type u} [Field k]
    [Algebra k (X.presheaf.stalk (pullback.fst f g x))]
    [Algebra k (Y.presheaf.stalk (pullback.snd f g x))]
    (φ : (X.presheaf.stalk (pullback.fst f g x)) ⊗[k]
      (Y.presheaf.stalk (pullback.snd f g x)) →+* (pullback f g).presheaf.stalk x)
    (hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom = ((pullback.fst f g).stalkMap x).hom)
    (hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom =
      ((pullback.snd f g).stalkMap x).hom)
    (y : pullback (C := Scheme) (i ≫ f) (j ≫ g))
    (hy : x = Scheme.Hom.productClosedMap f g i j y) :
    (ModuleCat.extendScalars φ).obj
      (ModuleCat.exteriorTensorObj k
        (ModuleCat.of (X.presheaf.stalk (pullback.fst f g x))
          (X.presheaf.stalk (pullback.fst f g x) ⧸ IdealSheafData.stalk i.ker (pullback.fst f g x)))
        (ModuleCat.of (Y.presheaf.stalk (pullback.snd f g x))
          (Y.presheaf.stalk (pullback.snd f g x) ⧸
            IdealSheafData.stalk j.ker (pullback.snd f g x)))) ≅
      (ModuleCat.restrictScalars
        (transportedClosedStalkMap (Scheme.Hom.productClosedMap f g i j) y x hy)).obj
          (ModuleCat.of ((pullback (i ≫ f) (j ≫ g)).presheaf.stalk y)
            ((pullback (i ≫ f) (j ≫ g)).presheaf.stalk y)) := by
  let I := IdealSheafData.stalk i.ker (pullback.fst f g x)
  let J := IdealSheafData.stalk j.ker (pullback.snd f g x)
  let R := (pullback f g).presheaf.stalk x
  let r := Scheme.Hom.productClosedMap f g i j
  exact ModuleCat.Tor.extendExteriorTensorObjQuotientIso (k := k) φ I J ≪≫
    LinearEquiv.toModuleIso (Ideal.quotientEquivAlgOfEq R
      (productClosedMap_idealStalk_eq_map_productIdeal f g i j x φ hleft hright).symm).toLinearEquiv
      ≪≫ quotientIsoTransportedClosedStalk r y x hy

end Stacks.Chow
