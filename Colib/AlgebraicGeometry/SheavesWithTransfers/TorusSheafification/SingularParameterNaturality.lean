/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.ParameterNaturality
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedWindow
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.ParameterNaturality
import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# Parameter maps on the original singular torus comparison

The parameter-map square follows from the same signed permutation of
the native simplex and parameter. Its extension by zero is the actual
weight-zero comparison on the sheafified cochain complexes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme
open Stacks.DerivedIndexing

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

/-- Apply the original parameter sheafification comparison termwise. -/
def parameterSectionsSheafificationComplexMap
    (V : SmoothSite (Spec (.of k))) [GeometricallyIntegral V.hom]
    {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (PresheafWithTransfers.{u + 1} k) c) :
    ((nisnevichSheafify k).mapHomologicalComplex c).obj
        (((withParameterFunctor V).mapHomologicalComplex c).obj K) ⟶
      ((parameterSectionsFunctor k V).mapHomologicalComplex c).obj
        (((nisnevichSheafify k).mapHomologicalComplex c).obj K) where
  f i := parameterSectionsSheafificationComparison k V (K.X i)
  comm' i j _ := (parameterSectionsSheafificationComparison_naturality k V (K.d i j)).symm

variable {V W : SmoothSite (Spec (.of k))}
  [GeometricallyIntegral V.hom] [GeometricallyIntegral W.hom]

/-- The actual parameter-map square on the original complexes. -/
@[reassoc]
theorem parameterSectionsSheafificationComplexMap_parameterMap (f : V ⟶ W)
    {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (PresheafWithTransfers.{u + 1} k) c) :
    ((nisnevichSheafify k).mapHomologicalComplex c).map
        (((withParameterPullbackNatTrans f).mapHomologicalComplex c).app K) ≫
      parameterSectionsSheafificationComplexMap k V c K =
    parameterSectionsSheafificationComplexMap k W c K ≫
      ((parameterSectionsPullbackNatTrans k f).mapHomologicalComplex c).app
        (((nisnevichSheafify k).mapHomologicalComplex c).obj K) := by
  ext i : 1
  exact parameterSectionsSheafificationComparison_parameterMap k f (K.X i)

variable (V)

/-- The signed comparison on the original singular chain complex. -/
def singularSheafParameterSectionsMap (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafComplex k (withParameter P V) ⟶
      ((parameterSectionsFunctor k V).mapHomologicalComplex (.down ℕ)).obj
        (singularSheafComplex k P) :=
  ((nisnevichSheafify k).mapHomologicalComplex (.down ℕ)).map
      (withParameterSingularComplexIso P V).inv ≫
    parameterSectionsSheafificationComplexMap k V (.down ℕ) (singularComplex P)

/-- The signed comparison on the original weight-zero cochain complex. -/
def singularSheafCochainParameterSectionsMap (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafCochainComplex k (withParameter P V) 0 ⟶
      ((parameterSectionsFunctor k V).mapHomologicalComplex (.up ℤ)).obj
        (singularSheafCochainComplex k P 0) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let A := nisnevichSheafify k
  let B := parameterSectionsFunctor k V
  exact (mapExtendIso A e (singularComplex (withParameter P V))).inv ≫
    (e.extendFunctor _).map (singularSheafParameterSectionsMap k V P) ≫
    (mapExtendIso B e (singularSheafComplex k P)).hom ≫
    (B.mapHomologicalComplex (.up ℤ)).map (mapExtendIso A e (singularComplex P)).hom

/-- In the torus case this is precisely the previously defined comparison. -/
theorem singularSheafCochainParameterSectionsMap_torus (P : PresheafWithTransfers.{u + 1} k) :
    singularSheafCochainParameterSectionsMap k (SmoothSite.multiplicativeGroupObject (Spec (.of k)))
      P = singularSheafCochainTorusSectionsMap k P := rfl

variable {V}

/-- The original chain comparison commutes with the actual parameter pullback. -/
@[reassoc]
theorem singularSheafParameterSectionsMap_parameterMap (f : V ⟶ W)
    (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafFunctor k).map (parameterPullback P f) ≫
        singularSheafParameterSectionsMap k V P =
      singularSheafParameterSectionsMap k W P ≫
        ((parameterSectionsPullbackNatTrans k f).mapHomologicalComplex (.down ℕ)).app
          (singularSheafComplex k P) := by
  let A := (nisnevichSheafify k).mapHomologicalComplex (.down ℕ)
  let e₁ := (withParameterSingularComplexIso P V).inv
  let e₂ := (withParameterSingularComplexIso P W).inv
  let r := singularComplexMap (parameterPullback P f)
  let t := ((withParameterPullbackNatTrans f).mapHomologicalComplex (.down ℕ)).app
    (singularComplex P)
  let η₁ := parameterSectionsSheafificationComplexMap k V (.down ℕ) (singularComplex P)
  let η₂ := parameterSectionsSheafificationComplexMap k W (.down ℕ) (singularComplex P)
  let β := ((parameterSectionsPullbackNatTrans k f).mapHomologicalComplex (.down ℕ)).app
    (singularSheafComplex k P)
  change A.map r ≫ (A.map e₁ ≫ η₁) = (A.map e₂ ≫ η₂) ≫ β
  calc
    _ = A.map (r ≫ e₁) ≫ η₁ :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ η₁) (A.map_comp _ _).symm)
    _ = A.map (e₂ ≫ t) ≫ η₁ :=
      congrArg (fun m => A.map m ≫ η₁) (withParameterSingularComplexIso_inv_parameterMap P f)
    _ = A.map e₂ ≫ (A.map t ≫ η₁) :=
      (congrArg (· ≫ η₁) (A.map_comp _ _)).trans (Category.assoc _ _ _)
    _ = _ := (congrArg (A.map e₂ ≫ ·)
      (parameterSectionsSheafificationComplexMap_parameterMap k f (.down ℕ)
        (singularComplex P))).trans (Category.assoc _ _ _).symm

/-- The placed signed comparison commutes with the actual parameter pullback. -/
@[reassoc]
theorem singularSheafCochainParameterSectionsMap_parameterMap (f : V ⟶ W)
    (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafCochainFunctor k 0).map (parameterPullback P f) ≫
        singularSheafCochainParameterSectionsMap k V P =
      singularSheafCochainParameterSectionsMap k W P ≫
        ((parameterSectionsPullbackNatTrans k f).mapHomologicalComplex (.up ℤ)).app
          (singularSheafCochainComplex k P 0) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let A := nisnevichSheafify k
  let V' := parameterSectionsFunctor k V
  let W' := parameterSectionsFunctor k W
  let E := e.extendFunctor (SheafWithTransfers.{u + 1} k)
  let D := e.extendFunctor (PresheafWithTransfers.{u + 1} k)
  let K := singularComplex P
  let L₁ := singularComplex (withParameter P V)
  let L₂ := singularComplex (withParameter P W)
  let a := mapExtendIso A e K
  let a₁ := mapExtendIso A e L₁
  let a₂ := mapExtendIso A e L₂
  let b₁ := mapExtendIso V' e (singularSheafComplex k P)
  let b₂ := mapExtendIso W' e (singularSheafComplex k P)
  let r := singularComplexMap (parameterPullback P f)
  let A₁ := A.mapHomologicalComplex (.up ℤ)
  let V₁ := V'.mapHomologicalComplex (.up ℤ)
  let W₁ := W'.mapHomologicalComplex (.up ℤ)
  let β := parameterSectionsPullbackNatTrans k f
  let β₀ := β.mapHomologicalComplex (.down ℕ)
  let β₁ := β.mapHomologicalComplex (.up ℤ)
  let m₁ := singularSheafParameterSectionsMap k V P
  let m₂ := singularSheafParameterSectionsMap k W P
  have hA : A₁.map (D.map r) ≫ a₁.inv = a₂.inv ≫ E.map
      ((A.mapHomologicalComplex (.down ℕ)).map r) := (mapExtendNatIso A e).inv.naturality r
  have hβ : E.map (β₀.app (singularSheafComplex k P)) ≫ b₁.hom =
      b₂.hom ≫ β₁.app (E.obj (singularSheafComplex k P)) :=
    mapExtendIso_hom_natTrans β e (singularSheafComplex k P)
  have hβ' : β₁.app (E.obj (singularSheafComplex k P)) ≫ V₁.map a.hom =
      W₁.map a.hom ≫ β₁.app (singularSheafCochainComplex k P 0) :=
    (β₁.naturality a.hom).symm
  have hM : E.map ((A.mapHomologicalComplex (.down ℕ)).map r) ≫ E.map m₁ =
      E.map m₂ ≫ E.map (β₀.app (singularSheafComplex k P)) :=
    (E.map_comp _ _).symm.trans
      ((congrArg E.map (singularSheafParameterSectionsMap_parameterMap k f P)).trans
        (E.map_comp _ _))
  change A₁.map (D.map r) ≫ (a₁.inv ≫ E.map m₁ ≫ b₁.hom ≫ V₁.map a.hom) =
    (a₂.inv ≫ E.map m₂ ≫ b₂.hom ≫ W₁.map a.hom) ≫
      β₁.app (singularSheafCochainComplex k P 0)
  simp only [Category.assoc, reassoc_of% hA, reassoc_of% hM, reassoc_of% hβ, hβ']

end AlgebraicGeometry.SheafWithTransfers
