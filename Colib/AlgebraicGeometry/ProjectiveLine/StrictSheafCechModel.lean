/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.VectorBundleCechModel
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.AffineFiniteProjective
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Qcoh
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties

/-! # Strictly perfect sheaf models of the projective-line Čech complex

The affine tilde counit identifies the complex of sections, after applying
tilde degreewise, with the actual signed Čech complex of sheaves. The finite
projective model therefore gives a strictly perfect sheaf model in the same
degrees, up to chain homotopy, over an arbitrary commutative ring.

## References
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Stacks.AlgebraicGeometry.FlatBaseChange (isQuasicoherent_pushforward_of_qcqs)

universe u v u' v'

private def singleArrowIso {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : a.hom ≫ g = f ≫ b.hom) :
    Arrow.mk ((single C (.up ℤ) 0).map f) ≅ Arrow.mk ((single C (.up ℤ) 0).map g) :=
  Arrow.isoMk ((single C (.up ℤ) 0).mapIso a) ((single C (.up ℤ) 0).mapIso b)
    (by
      change (single C (.up ℤ) 0).map a.hom ≫ (single C (.up ℤ) 0).map g =
        (single C (.up ℤ) 0).map f ≫ (single C (.up ℤ) 0).map b.hom
      rw [← Functor.map_comp, ← Functor.map_comp, h])

private def mapShiftedSingleConeIso {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive] {A B : C} (f : A ⟶ B) :
    (F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.mappingCone ((single C (.up ℤ) 0).map f))⟦(-1 : ℤ)⟧) ≅
      (CochainComplex.mappingCone ((single D (.up ℤ) 0).map (F.map f)))⟦(-1 : ℤ)⟧ := by
  let S := singleMapHomologicalComplex F (.up ℤ) 0
  exact ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (-1 : ℤ)).app _ ≪≫
    (shiftFunctor (CochainComplex D ℤ) (-1 : ℤ)).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso ((single C (.up ℤ) 0).map f) F ≪≫
        homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
          (Arrow.isoMk (S.app A) (S.app B) (S.hom.naturality f).symm))

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

variable (R : CommRingCat.{u}) (M : (line R).Modules)

/-- The actual signed Čech complex of sheaves on the affine coefficient base. -/
abbrev lineSheafCechComplex : CochainComplex (Spec R).Modules ℤ :=
  (CochainComplex.mappingCone
    ((single (Spec R).Modules (.up ℤ) 0).map
      ((Scheme.Modules.pushforward (lineProjection R)).map
        (Scheme.Modules.twoOpenCech (lineChartZero R) (lineChartOne R) M).g)))⟦(-1 : ℤ)⟧

/-- Applying tilde to the signed complex of sections recovers the signed sheaf complex. -/
def lineSheafCechSectionsIso [M.IsQuasicoherent] :
    ((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj (lineCechSectionsComplex R M) ≅
      lineSheafCechComplex R M := by
  let U := lineChartZero R
  let V := lineChartOne R
  let S := Scheme.Modules.twoOpenCech U V M
  let p := lineProjection R
  let G := Scheme.Modules.pushforward p
  let s := G.map S.g
  have qU : ((restrictPushMod U).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs U.ι (M.restrict U.ι)
  have qV : ((restrictPushMod V).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs V.ι (M.restrict V.ι)
  have q₂ : S.X₂.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.RelativeMayerVietoris.isQuasicoherent_biprod _ _ qU qV
  have q₃ : S.X₃.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs (U ⊓ V).ι (M.restrict (U ⊓ V).ι)
  let : (G.obj S.X₂).IsQuasicoherent := isQuasicoherent_pushforward_of_qcqs p S.X₂
  let : (G.obj S.X₃).IsQuasicoherent := isQuasicoherent_pushforward_of_qcqs p S.X₃
  let h₂ : IsIso (G.obj S.X₂).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mp inferInstance
  let h₃ : IsIso (G.obj S.X₃).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mp inferInstance
  let a := Functor.isoWhiskerLeft G (moduleSpecΓIsoGlobalSectionsOver R) ≪≫
    globalSectionsOverPushforwardNatIso p (𝟙 (Spec R)) p (Category.comp_id p)
  let e₂ := ((tilde.functor R).mapIso (a.app S.X₂)).symm ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (G.obj S.X₂)) h₂
  let e₃ := ((tilde.functor R).mapIso (a.app S.X₃)).symm ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (G.obj S.X₃)) h₃
  have he : e₂.hom ≫ s =
      (tilde.functor R).map ((globalSectionsOver p).map S.g) ≫ e₃.hom := by
    let F := tilde.functor R
    let H := moduleSpecΓFunctor (R := R)
    let c₂ : F.obj (H.obj (G.obj S.X₂)) ⟶ G.obj S.X₂ := (G.obj S.X₂).fromTildeΓ
    let c₃ : F.obj (H.obj (G.obj S.X₃)) ⟶ G.obj S.X₃ := (G.obj S.X₃).fromTildeΓ
    have hn : c₂ ≫ s = F.map (H.map s) ≫ c₃ := by
      exact (Scheme.Modules.fromTildeΓNatTrans.naturality s).symm
    have ha : a.inv.app S.X₂ ≫ H.map s =
        (globalSectionsOver p).map S.g ≫ a.inv.app S.X₃ := by
      exact (a.inv.naturality S.g).symm
    change (F.map (a.inv.app S.X₂) ≫ c₂) ≫ s =
      F.map ((globalSectionsOver p).map S.g) ≫ F.map (a.inv.app S.X₃) ≫ c₃
    calc
      _ = F.map (a.inv.app S.X₂ ≫ H.map s) ≫ c₃ := by
        rw [Category.assoc, hn, Functor.map_comp, Category.assoc]
      _ = _ := by rw [ha, Functor.map_comp, Category.assoc]
  exact mapShiftedSingleConeIso (tilde.functor R) ((globalSectionsOver p).map S.g) ≪≫
    (shiftFunctor (CochainComplex (Spec R).Modules ℤ) (-1 : ℤ)).mapIso
      (homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
        (singleArrowIso _ _ e₂ e₃ he))

/-- The actual signed sheaf Čech complex of a vector bundle has a strictly perfect
two-term model, up to chain homotopy. -/
theorem exists_lineStrictSheafCechModel [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    ∃ P : CochainComplex (Spec R).Modules ℤ,
      StrictlyPerfect.IsStrictlyPerfect (X := (Spec R).toRingedSpace) P ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i)) ∧
      Nonempty (HomotopyEquiv (lineSheafCechComplex R M) P) := by
  let : M.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M
  obtain ⟨P, hP, hfp, ⟨h⟩⟩ := exists_lineCechFiniteProjectiveModel R M
  have hbdd : {i : ℤ | ¬ IsZero (P.X i)}.Finite := by
    refine (show ({0, 1} : Set ℤ).Finite by simp).subset ?_
    intro i hi
    by_contra hn
    exact hi (hP i (fun e ↦ hn (by simp [e])) (fun e ↦ hn (by simp [e])))
  refine ⟨((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj P,
    Stacks.AffineTilde.isStrictlyPerfect_tildeComplex_of_projective P hbdd hfp, ?_, ?_⟩
  · exact fun i h₀ h₁ ↦ (tilde.functor R).map_isZero (hP i h₀ h₁)
  · exact ⟨(HomotopyEquiv.ofIso (lineSheafCechSectionsIso R M).symm).trans
      ((tilde.functor R).mapHomotopyEquiv h)⟩


/-- The derived direct image of the original sheaf in degree zero. -/
abbrev lineVectorBundleDerivedImage :=
  DerivedCategory.Plus.ι.obj
    ((Scheme.Modules.pushforward (lineProjection R)).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (line R).Modules 0).obj M))

/-- A chain homotopy model of the actual sheaf Čech complex represents the
derived direct image, by the original signed cone comparison. -/
def lineDerivedImageIsoOfSheafCechModel [M.IsQuasicoherent]
    {P : CochainComplex (Spec R).Modules ℤ}
    (h : HomotopyEquiv (lineSheafCechComplex R M) P) :
    lineVectorBundleDerivedImage R M ≅ DerivedCategory.Q.obj P := by
  let Q := DerivedCategory.Q (C := (Spec R).Modules)
  let hQ : IsIso (Q.map h.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Spec R).Modules h.hom).mpr h.quasiIso_hom
  exact lineDerivedCechConeIso R M ≪≫ @asIso _ _ _ _ (Q.map h.hom) hQ

/-- The derived direct image of a vector bundle on the projective line has a
strictly perfect representative concentrated in degrees zero and one. -/
theorem exists_lineDerivedImageStrictModel [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    ∃ P : CochainComplex (Spec R).Modules ℤ,
      StrictlyPerfect.IsStrictlyPerfect (X := (Spec R).toRingedSpace) P ∧
      (∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero (P.X i)) ∧
      Nonempty (lineVectorBundleDerivedImage R M ≅ DerivedCategory.Q.obj P) := by
  let : M.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M
  obtain ⟨P, hP, hb, ⟨h⟩⟩ := exists_lineStrictSheafCechModel R M
  exact ⟨P, hP, hb, ⟨lineDerivedImageIsoOfSheafCechModel R M h⟩⟩

set_option maxHeartbeats 1400000 in
-- Unfolding the native sheaf and derived-category instances needs additional heartbeats.
/-- The derived direct image of a projective-line vector bundle is perfect
as a native object of the derived category on the coefficient scheme. -/
theorem isPerfect_lineVectorBundleDerivedImage [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    RingedSpace.IsPerfect (X := (Spec R).toRingedSpace) (lineVectorBundleDerivedImage R M) := by
  obtain ⟨P, hP, _, ⟨e⟩⟩ := exists_lineDerivedImageStrictModel R M
  have hQ : RingedSpace.IsPerfect (X := (Spec R).toRingedSpace)
      ((DerivedCategory.Q (C := (Spec R).Modules)).obj P) :=
    RingedSpace.isPerfect_Q_obj_of_isStrictlyPerfect (X := (Spec R).toRingedSpace) hP
  exact isPerfect_of_iso_scheme (S := Spec R) e.symm hQ

end AlgebraicGeometry.projectiveSpaceOver
