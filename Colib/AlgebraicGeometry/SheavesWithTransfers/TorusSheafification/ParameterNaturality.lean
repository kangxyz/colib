/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterFunctor.ParameterNaturality

/-!
# Parameter maps on the actual coefficient sheafification comparison

The original sheafification unit supplies this comparison for every
geometrically integral smooth parameter. Its square with a parameter
map follows from the original coefficient naturality of that pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  (V : SmoothSite (Spec (.of k))) [GeometricallyIntegral V.hom]

/-- Restrict the actual transfer coefficient along the original product
with the parameter, preserving the Nisnevich sheaf condition. -/
def parameterSectionsFunctor : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k where
  obj F := ⟨withParameter F.obj V, withParameter_isNisnevichSheaf F.obj F.property V⟩
  map f := ObjectProperty.homMk (withParameterMap f.hom V)
  map_id _ := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    rfl

instance : (parameterSectionsFunctor k V).Additive where
  map_add := by
    intro P Q f g
    apply ObjectProperty.hom_ext
    rfl

/-- At the torus the generic parameter reindexing has exactly the chosen
objects and maps of the original torus functor. -/
def parameterSectionsFunctorTorusIso :
    parameterSectionsFunctor k (SmoothSite.multiplicativeGroupObject (Spec (.of k))) ≅
      (torusSectionsFunctor k : SheafWithTransfers.{u + 1} k ⥤ _) := Iso.refl _

/-- The actual coefficient comparison for any smooth integral parameter. -/
def parameterSectionsSheafificationComparison (P : PresheafWithTransfers.{u + 1} k) :
    (nisnevichSheafify k).obj (withParameter P V) ⟶
      (parameterSectionsFunctor k V).obj ((nisnevichSheafify k).obj P) :=
  nisnevichSheafifyLift k (withParameterMap (toNisnevichSheafify k P) V)

@[reassoc]
theorem parameterSectionsSheafificationComparison_unit (P : PresheafWithTransfers.{u + 1} k) :
    toNisnevichSheafify k (withParameter P V) ≫
      (parameterSectionsSheafificationComparison k V P).hom =
        withParameterMap (toNisnevichSheafify k P) V :=
  toNisnevichSheafify_lift k _

/-- This coefficient comparison is the chosen original torus comparison
when the parameter is the native multiplicative group. -/
theorem parameterSectionsSheafificationComparison_torus (P : PresheafWithTransfers.{u + 1} k) :
    parameterSectionsSheafificationComparison k
      (SmoothSite.multiplicativeGroupObject (Spec (.of k))) P =
        torusSectionsSheafificationComparison k P := rfl

/-- The coefficient comparison is natural for the original coefficient map. -/
@[reassoc]
theorem parameterSectionsSheafificationComparison_naturality
    {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    (nisnevichSheafify k).map (withParameterMap f V) ≫
        parameterSectionsSheafificationComparison k V Q =
      parameterSectionsSheafificationComparison k V P ≫
        (parameterSectionsFunctor k V).map ((nisnevichSheafify k).map f) := by
  apply nisnevichSheafify_hom_ext k
  let A := nisnevichSheafify k
  let ηP := toNisnevichSheafify k P
  let ηQ := toNisnevichSheafify k Q
  let t := withParameterMap f V
  let x := parameterSectionsSheafificationComparison k V P
  let y := parameterSectionsSheafificationComparison k V Q
  let ηV := toNisnevichSheafify k (withParameter P V)
  let ηV' := toNisnevichSheafify k (withParameter Q V)
  let s := withParameterMap (A.map f).hom V
  change ηV ≫ ((A.map t).hom ≫ y.hom) = ηV ≫ (x.hom ≫ s)
  calc
    _ = (ηV ≫ (A.map t).hom) ≫ y.hom := (Category.assoc _ _ _).symm
    _ = (t ≫ ηV') ≫ y.hom := congrArg (· ≫ y.hom) (toNisnevichSheafify_naturality k t).symm
    _ = t ≫ withParameterMap ηQ V :=
      (Category.assoc _ _ _).trans
        (congrArg (t ≫ ·) (parameterSectionsSheafificationComparison_unit k V Q))
    _ = withParameterMap ηP V ≫ s := by
      let F := withParameterFunctor V
      change F.map f ≫ F.map ηQ = F.map ηP ≫ F.map (A.map f).hom
      rw [← F.map_comp, ← F.map_comp, toNisnevichSheafify_naturality k f]
    _ = _ := (congrArg (· ≫ s) (parameterSectionsSheafificationComparison_unit k V P).symm).trans
      (Category.assoc _ _ _)

variable {V} {W : SmoothSite (Spec (.of k))} [GeometricallyIntegral W.hom]

/-- The actual pullback of a parameter preserves the sheaf condition and
uses the original signed maps. -/
def parameterSectionsPullbackNatTrans (f : V ⟶ W) :
    parameterSectionsFunctor k W ⟶ parameterSectionsFunctor k V where
  app F := ObjectProperty.homMk (parameterPullback F.obj f)
  naturality _ _ g := by
    apply ObjectProperty.hom_ext
    exact (parameterPullback_coefficient_naturality g.hom f).symm

/-- The coefficient comparison commutes with the actual parameter pullback. -/
@[reassoc]
theorem parameterSectionsSheafificationComparison_parameterMap
    (f : V ⟶ W) (P : PresheafWithTransfers.{u + 1} k) :
    (nisnevichSheafify k).map (parameterPullback P f) ≫
        parameterSectionsSheafificationComparison k V P =
      parameterSectionsSheafificationComparison k W P ≫
        (parameterSectionsPullbackNatTrans k f).app ((nisnevichSheafify k).obj P) := by
  apply nisnevichSheafify_hom_ext k
  let A := nisnevichSheafify k
  let η := toNisnevichSheafify k P
  let g := parameterPullback P f
  let x := parameterSectionsSheafificationComparison k V P
  let y := parameterSectionsSheafificationComparison k W P
  let ηW := toNisnevichSheafify k (withParameter P W)
  let ηV := toNisnevichSheafify k (withParameter P V)
  let t := parameterPullback (A.obj P).obj f
  change ηW ≫ ((A.map g).hom ≫ x.hom) = ηW ≫ (y.hom ≫ t)
  calc
    _ = (ηW ≫ (A.map g).hom) ≫ x.hom := (Category.assoc _ _ _).symm
    _ = (g ≫ ηV) ≫ x.hom := congrArg (· ≫ x.hom) (toNisnevichSheafify_naturality k g).symm
    _ = g ≫ withParameterMap η V :=
      (Category.assoc _ _ _).trans
        (congrArg (g ≫ ·) (parameterSectionsSheafificationComparison_unit k V P))
    _ = withParameterMap η W ≫ t := parameterPullback_coefficient_naturality η f
    _ = _ := (congrArg (· ≫ t) (parameterSectionsSheafificationComparison_unit k W P).symm).trans
      (Category.assoc _ _ _)

end AlgebraicGeometry.SheafWithTransfers
