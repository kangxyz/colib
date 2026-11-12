/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderReducedChains
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
import Colib.Algebra.Homology.Embedding.MapExtend
import Colib.AlgebraicTopology.DoldKan.NormalizedMooreMap

/-!
# Reduced presheaf cochains of a representable parameter cylinder

The comparison of the reduced simplicial abelian presheaves passes through
normalized Moore chains and extension to nonpositive cochain degrees.
Both comparisons retain the fold induced by the original cylinder projection.
-/

@[expose] public noncomputable section

open AlgebraicTopology CategoryTheory Limits Opposite
open scoped Simplicial

universe z a w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- The reduced presheaf chains placed in nonpositive cochain degrees. -/
def reducedPresheafCochains (C : Type u) [Category.{v} C] :
    PointedSimplicialPresheaf.{w} C ⥤ CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ :=
  reducedChains C ⋙ (ComplexShape.embeddingUpIntLE 0).extendFunctor _

namespace ParameterCoproduct

variable (V : C) (A : Type z) [Category.{a} A] [Preadditive A] [HasCoproducts.{v} A]

/-- Apply the original parameter fold in each degree of a homological complex. -/
def homologicalFold {ι : Type*} (c : ComplexShape ι) :
    (functor V A).mapHomologicalComplex c ⟶ 𝟭 _ :=
  NatTrans.mapHomologicalComplex (fold V A) c ≫ (Functor.mapHomologicalComplexIdIso _ c).hom

@[simp]
theorem homologicalFold_app_f {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (Cᵒᵖ ⥤ A) c) (i : ι) :
    ((homologicalFold V A c).app K).f i = (fold V A).app (K.X i) := by
  simp [homologicalFold]

end ParameterCoproduct

variable (V : C)

private theorem normalizedParameterCoproduct_hom_fold
    (R : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{max v w})) :
    let A := Cᵒᵖ ⥤ AddCommGrpCat.{max v w}
    let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
    (normalizedMooreComplexCompMapHomologicalComplexIso Φ).hom.app R ≫
        (normalizedMooreComplex A).map ((ParameterCoproduct.simplicialFold V _).app R) =
      (ParameterCoproduct.homologicalFold V _ (.down ℕ)).app
        ((normalizedMooreComplex A).obj R) := by
  let A := Cᵒᵖ ⥤ AddCommGrpCat.{max v w}
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let S := ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}
  let e := normalizedMooreComplexCompMapHomologicalComplexIso Φ
  let i := inclusionOfMooreComplex A
  let N := normalizedMooreComplex A
  let L := alternatingFaceMapComplex A
  let f := (ParameterCoproduct.simplicialFold V AddCommGrpCat.{max v w}).app R
  change e.hom.app R ≫ N.map f =
    (ParameterCoproduct.homologicalFold V _ (.down ℕ)).app (N.obj R)
  let : Mono (i.app R) := inferInstanceAs (Mono (inclusionOfMooreComplexMap R))
  have hi : N.map f ≫ i.app R = i.app (S.obj R) ≫ L.map f := i.naturality f
  let j := (Φ.mapHomologicalComplex (.down ℕ)).map (i.app R)
  let r := (alternatingFaceMapComplexCompMapHomologicalComplexIso Φ).hom.app R
  have h := congr_app
    (normalizedMooreComplexCompMapHomologicalComplexIso_hom_comp_inclusionOfMooreComplex Φ) R
  change e.hom.app R ≫ i.app (S.obj R) = j ≫ r at h
  apply (cancel_mono (i.app R)).1
  calc
    _ = (e.hom.app R ≫ i.app (S.obj R)) ≫ L.map f :=
      (Category.assoc _ _ _).trans
        ((congrArg (e.hom.app R ≫ ·) hi).trans (Category.assoc _ _ _).symm)
    _ = (j ≫ r) ≫ L.map f := congrArg (· ≫ L.map f) h
    _ = _ := by
      apply HomologicalComplex.hom_ext
      intro n
      change (Φ.map ((i.app R).f n) ≫ 𝟙 _) ≫
          (ParameterCoproduct.fold V _).app (R.obj (op ⦋n⦌)) =
        ((ParameterCoproduct.homologicalFold V _ (.down ℕ)).app (N.obj R)).f n ≫ (i.app R).f n
      simp only [Category.comp_id, ParameterCoproduct.homologicalFold_app_f]
      exact (ParameterCoproduct.fold V _).naturality ((i.app R).f n)

private def reducedChainsParameterCylinderIso (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedChains C).obj (parameterizedCylinder X (liftedRepresentableInterval.{w} V)) ≅
      ((ParameterCoproduct.functor V AddCommGrpCat.{max v w}).mapHomologicalComplex (.down ℕ)).obj
        ((reducedChains C).obj X) :=
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let R := (reducedFreeAbelian C).obj X
  (normalizedMooreComplex _).mapIso (reducedFreeAbelianParameterCylinderIso.{w} V X) ≪≫
    ((normalizedMooreComplexCompMapHomologicalComplexIso Φ).app R).symm

private theorem reducedChainsParameterCylinderIso_hom_fold
    (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedChainsParameterCylinderIso.{w} V X).hom ≫
        (ParameterCoproduct.homologicalFold V _ (.down ℕ)).app ((reducedChains C).obj X) =
      (reducedChains C).map (cylinderProjection X (liftedRepresentableInterval.{w} V)) := by
  let I := liftedRepresentableInterval.{w} V
  let A := Cᵒᵖ ⥤ AddCommGrpCat.{max v w}
  let N := normalizedMooreComplex A
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let R := (reducedFreeAbelian C).obj X
  let e := (normalizedMooreComplexCompMapHomologicalComplexIso Φ).app R
  let s := reducedFreeAbelianParameterCylinderIso.{w} V X
  let f := (ParameterCoproduct.simplicialFold V AddCommGrpCat.{max v w}).app R
  have hf : e.hom ≫ N.map f =
      (ParameterCoproduct.homologicalFold V _ (.down ℕ)).app (N.obj R) :=
    normalizedParameterCoproduct_hom_fold V R
  change (N.map s.hom ≫ e.inv) ≫
      (ParameterCoproduct.homologicalFold V _ (.down ℕ)).app (N.obj R) =
    N.map ((reducedFreeAbelian C).map (cylinderProjection X I))
  calc
    _ = N.map s.hom ≫ e.inv ≫ e.hom ≫ N.map f :=
      (Category.assoc _ _ _).trans (congrArg (fun t => N.map s.hom ≫ e.inv ≫ t) hf.symm)
    _ = N.map s.hom ≫ N.map f :=
      congrArg (N.map s.hom ≫ ·) (e.inv_hom_id_assoc (N.map f))
    _ = _ := (N.map_comp _ _).symm.trans
      (N.congr_map (reducedFreeAbelianParameterCylinderIso_hom_fold V X))

private theorem mapExtendIso_hom_fold {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (e : c.Embedding c')
    (K : HomologicalComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) c) :
    let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
    (K.mapExtendIso Φ e).hom ≫
        (e.extendFunctor _).map ((ParameterCoproduct.homologicalFold V _ c).app K) =
      (ParameterCoproduct.homologicalFold V _ c').app (K.extend e) := by
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let f := (ParameterCoproduct.homologicalFold V AddCommGrpCat.{max v w} c).app K
  apply HomologicalComplex.hom_ext
  intro j
  change (K.mapExtendIso Φ e).hom.f j ≫ (HomologicalComplex.extendMap f e).f j =
    ((ParameterCoproduct.homologicalFold V _ c').app (K.extend e)).f j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    let L := (Φ.mapHomologicalComplex c).obj K
    let s := L.extendXIso e hi
    let t := K.extendXIso e hi
    let a := K.mapExtendIso Φ e
    let φ := ParameterCoproduct.fold V AddCommGrpCat.{max v w}
    have hf : (HomologicalComplex.extendMap f e).f j = s.hom ≫ f.f i ≫ t.inv :=
      HomologicalComplex.extendMap_f f e hi
    have hs : a.hom.f j ≫ s.hom = Φ.map t.hom :=
      K.mapExtendIso_hom_f_extendXIso Φ e hi
    have hfi : f.f i = φ.app (K.X i) := ParameterCoproduct.homologicalFold_app_f V _ c K i
    have hfj : ((ParameterCoproduct.homologicalFold V _ c').app (K.extend e)).f j =
        φ.app ((K.extend e).X j) :=
      ParameterCoproduct.homologicalFold_app_f V _ c' (K.extend e) j
    apply (cancel_mono t.hom).1
    calc
      _ = (a.hom.f j ≫ (s.hom ≫ f.f i ≫ t.inv)) ≫ t.hom :=
        congrArg (fun p => (a.hom.f j ≫ p) ≫ t.hom) hf
      _ = (a.hom.f j ≫ s.hom) ≫ f.f i := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = Φ.map t.hom ≫ φ.app (K.X i) :=
        (congrArg (· ≫ f.f i) hs).trans (congrArg (Φ.map t.hom ≫ ·) hfi)
      _ = φ.app ((K.extend e).X j) ≫ t.hom := φ.naturality t.hom
      _ = _ := congrArg (· ≫ t.hom) hfj.symm
  · exact (K.isZero_extend_X e j (fun i hi => hj ⟨i, hi⟩)).eq_of_tgt _ _

/-- The reduced presheaf cochains of the actual pointed parameter cylinder
are the parameter coproduct of the reduced presheaf cochains. -/
@[no_expose]
def reducedPresheafCochainsParameterCylinderIso
    (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedPresheafCochains C).obj (parameterizedCylinder X (liftedRepresentableInterval.{w} V)) ≅
      ((ParameterCoproduct.functor V AddCommGrpCat.{max v w}).mapHomologicalComplex (.up ℤ)).obj
        ((reducedPresheafCochains C).obj X) :=
  let e := ComplexShape.embeddingUpIntLE 0
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  (e.extendFunctor _).mapIso (reducedChainsParameterCylinderIso.{w} V X) ≪≫
    (((reducedChains C).obj X).mapExtendIso Φ e).symm

/-- The literal pointed cylinder projection on reduced presheaf cochains
is the fold of the original parameter summands. -/
@[reassoc]
theorem reducedPresheafCochainsParameterCylinderIso_hom_fold
    (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedPresheafCochainsParameterCylinderIso.{w} V X).hom ≫
        (ParameterCoproduct.homologicalFold V _ (.up ℤ)).app ((reducedPresheafCochains C).obj X) =
      (reducedPresheafCochains C).map
        (cylinderProjection X (liftedRepresentableInterval.{w} V)) := by
  let I := liftedRepresentableInterval.{w} V
  let A := Cᵒᵖ ⥤ AddCommGrpCat.{max v w}
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let e := ComplexShape.embeddingUpIntLE 0
  let F := e.extendFunctor A
  let K := (reducedChains C).obj X
  let s := reducedChainsParameterCylinderIso.{w} V X
  let d := K.mapExtendIso Φ e
  let f := (ParameterCoproduct.homologicalFold V AddCommGrpCat.{max v w} (.down ℕ)).app K
  have hd : d.hom ≫ F.map f =
      (ParameterCoproduct.homologicalFold V _ (.up ℤ)).app (K.extend e) :=
    mapExtendIso_hom_fold V e K
  change (F.map s.hom ≫ d.inv) ≫
      (ParameterCoproduct.homologicalFold V _ (.up ℤ)).app (K.extend e) =
    F.map ((reducedChains C).map (cylinderProjection X I))
  calc
    _ = F.map s.hom ≫ d.inv ≫ d.hom ≫ F.map f :=
      (Category.assoc _ _ _).trans (congrArg (fun t => F.map s.hom ≫ d.inv ≫ t) hd.symm)
    _ = F.map s.hom ≫ F.map f :=
      congrArg (F.map s.hom ≫ ·) (d.inv_hom_id_assoc (F.map f))
    _ = _ := (F.map_comp _ _).symm.trans
      (F.congr_map (reducedChainsParameterCylinderIso_hom_fold V X))

end CategoryTheory.PointedSimplicialPresheaf
