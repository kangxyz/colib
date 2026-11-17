/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Native
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Parameter

/-!
# The tensor and the existing integral parameter functors

The tensor with a geometrically integral parameter acts by the original
native exterior map. The comparison is natural in every ordinary map of
such parameters, with identity components on the literal product objects.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- Tensoring on the right is the original fixed-parameter functor with identity components. -/
def tensorRightIsoParameterProduct (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] :
    tensorRight (Cor.mk T) ≅ parameterProduct T :=
  NatIso.ofComponents (fun X => Iso.refl (tensorObj X (Cor.mk T))) fun {X Y} a => by
    change (a ▷ Cor.mk T) ≫ 𝟙 (tensorObj Y (Cor.mk T)) =
      𝟙 (tensorObj X (Cor.mk T)) ≫ (parameterProduct T).map a
    have h : a ▷ Cor.mk T = (parameterProduct T).map a :=
      whiskerRight_eq_nativeExterior T a
    exact (Category.comp_id _).trans
      (h.trans (Category.id_comp ((parameterProduct T).map a)).symm)

@[simp]
theorem tensorRightIsoParameterProduct_hom_app (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] (X : Cor k) :
    (tensorRightIsoParameterProduct T).hom.app X = 𝟙 _ := rfl

/-- The tensor comparison intertwines the native graph map of parameters. -/
theorem tensorRightIsoParameterProduct_naturality {T T' : SmoothSite (Spec (.of k))}
    [GeometricallyIntegral T.hom] [GeometricallyIntegral T'.hom] (f : T ⟶ T') :
    (curriedTensor (Cor k)).flip.map ((graphFunctor k).map f) ≫
      (tensorRightIsoParameterProduct T').hom =
    (tensorRightIsoParameterProduct T).hom ≫ parameterProductMap f := by
  apply NatTrans.ext
  funext X
  change (rightExteriorParameterMap f).app X ≫ 𝟙 (tensorObj X (Cor.mk T')) =
    𝟙 (tensorObj X (Cor.mk T)) ≫
      (graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) f)
  exact (Category.comp_id _).trans
    ((rightExteriorParameterMap_app f X).trans (Category.id_comp _).symm)

end AlgebraicGeometry.Cor
