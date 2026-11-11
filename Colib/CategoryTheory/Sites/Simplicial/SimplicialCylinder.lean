/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Colib.CategoryTheory.Sites.Simplicial.MappingCofiber
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeContraction
import Mathlib.Topology.Homotopy.Contractible

/-!
# The pointed simplicial cylinder in the stalkwise localization

At each site point, the actual cylinder projection compares two pushout
squares along the basepoint axis. Its product and parameter projections are
realization weak equivalences, and both basepoint axes are split monomorphisms.
The projection is therefore invertible in the stalkwise localization, where
the two endpoint restrictions of a pointed cylinder map agree.
-/

@[expose] public noncomputable section

open CategoryTheory Limits CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

private theorem isRealizationWeakEquivalence_simplicialIntervalFst (Y : SSet.{w}) :
    SSet.IsRealizationWeakEquivalence (fst Y (Δ[1] : SSet.{w})) := by
  let : ContractibleSpace unitInterval := by
    apply (contractible_iff_id_nullhomotopic _).2
    refine ⟨0, ⟨ContinuousMap.Homotopy.symm ?_⟩⟩
    exact {
      toFun := fun z ↦ z.1 * z.2
      continuous_toFun := ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      map_zero_left := fun x ↦ zero_mul x
      map_one_left := fun x ↦ one_mul x }
  let : ContractibleSpace TopCat.I.{w} := TopCat.I.homeomorph.contractibleSpace
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit TopCat.I.{w}
  let p := ((ContinuousMap.HomotopyEquiv.refl |Y|).prodCongr e).trans
    (Homeomorph.prodUnique |Y| Unit).toHomotopyEquiv
  let E := (TopCat.homeoOfIso (SSet.realizationCylinderIso Y)).toHomotopyEquiv.trans p
  have h : E.toFun = (SSet.toTop.map (fst Y (Δ[1] : SSet.{w}))).hom := by
    rw [← SSet.realizationCylinderComparison_fst]
    rfl
  rw [SSet.IsRealizationWeakEquivalence, ← h]
  exact Topology.isWeakHomotopyEquivalence_of_homotopyEquiv E

variable {C : Type u} [Category.{v} C]

private theorem isRealizationWeakEquivalence_map_intervalFst
    (F : (Cᵒᵖ ⥤ SSet.{w}) ⥤ SSet.{w}) [PreservesFiniteProducts F]
    (e : (Functor.const Cᵒᵖ : SSet.{w} ⥤ _) ⋙ F ≅ 𝟭 _) (Y : Cᵒᵖ ⥤ SSet.{w}) :
    SSet.IsRealizationWeakEquivalence (F.map (prod.fst : Y ⨯ interval C ⟶ Y)) := by
  let a := (limit.isLimit (pair Y (interval C))).conePointUniqueUpToIso
    (tensorProductIsBinaryProduct Y (interval C))
  have ha : a.hom ≫ fst Y (interval C) = (prod.fst : Y ⨯ interval C ⟶ Y) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)
  rw [← ha, Functor.map_comp, ← intervalCylinderComparison_hom_fst F e Y]
  exact ((isRealizationWeakEquivalence_simplicialIntervalFst _).comp
    (SSet.IsRealizationWeakEquivalence.of_isIso _)).comp
    (SSet.IsRealizationWeakEquivalence.of_isIso _)

private theorem isRealizationWeakEquivalence_map_intervalCollapse
    (F : (Cᵒᵖ ⥤ SSet.{w}) ⥤ SSet.{w}) [PreservesFiniteProducts F]
    (e : (Functor.const Cᵒᵖ : SSet.{w} ⥤ _) ⋙ F ≅ 𝟭 _) :
    SSet.IsRealizationWeakEquivalence (F.map (terminal.from (interval.{w} C))) := by
  let T := ⊤_ (Cᵒᵖ ⥤ SSet.{w})
  let K := interval.{w} C
  let l : T ⨯ K ≅ K := Limits.prod.leftUnitor K
  have h : l.hom ≫ terminal.from K = (prod.fst : T ⨯ K ⟶ T) :=
    terminalIsTerminal.hom_ext _ _
  have hp := isRealizationWeakEquivalence_map_intervalFst F e T
  rw [← h, Functor.map_comp] at hp
  exact hp.of_comp_left (SSet.IsRealizationWeakEquivalence.of_isIso _)

variable (C) [LocallySmall.{w} C] (J : GrothendieckTopology C)

/-- The actual pointed simplicial cylinder projection is a stalkwise weak equivalence. -/
theorem stalkwiseWeakEquivalences_cylinderProjection_interval
    (X : PointedSimplicialPresheaf.{w} C) :
    stalkwiseWeakEquivalences C J (cylinderProjection X (interval C)) := by
  intro Φ
  let F := Φ.presheafFiber (A := SSet.{w})
  let e := Sites.constantPresheafFiberNatIso (D := SSet.{w}) Φ
  let K := interval.{w} C
  let i := intervalAxis X K
  let s := terminal.from K
  let p : X.right ⨯ K ⟶ X.right := prod.fst
  let q := cylinderProjection X K
  have hi : i ≫ (prod.snd : X.right ⨯ K ⟶ K) = 𝟙 K := prod.lift_snd _ _
  have hx : X.hom ≫ terminal.from X.right = 𝟙 _ := terminalIsTerminal.hom_ext _ _
  have hiF : F.map i ≫ F.map (prod.snd : X.right ⨯ K ⟶ K) = 𝟙 _ := by
    rw [← F.map_comp, hi, F.map_id]
  have hxF : F.map X.hom ≫ F.map (terminal.from X.right) = 𝟙 _ := by
    rw [← F.map_comp, hx, F.map_id]
  let : Mono (F.map i) := mono_of_mono_fac hiF
  let : Mono (F.map X.hom) := mono_of_mono_fac hxF
  have lower : IsPushout X.hom (𝟙 _) (𝟙 _) X.hom := IsPushout.of_id_snd
  change SSet.IsRealizationWeakEquivalence (F.map q.right)
  refine SSet.IsRealizationWeakEquivalence.pushout
    (F.map_isPushout (IsPushout.of_hasPushout i s)) (F.map_isPushout lower)
    (F.map s) (F.map p) (F.map (𝟙 _)) (F.map q.right) ?_ rfl ?_ ?_
    (isRealizationWeakEquivalence_map_intervalCollapse F e)
    (isRealizationWeakEquivalence_map_intervalFst F e X.right)
    (SSet.IsRealizationWeakEquivalence.of_isIso _)
  · simp only [← F.map_comp, i, p, s, intervalAxis, prod.lift_fst]
  · simp only [← F.map_comp, q, cylinderProjection, Under.homMk_right, pushout.inl_desc,
      Category.comp_id, p]
  · simp only [← F.map_comp, q, cylinderProjection, Under.homMk_right, pushout.inr_desc,
      Category.id_comp]

/-- The two actual endpoint restrictions of a pointed simplicial cylinder map agree locally. -/
theorem toStalkwiseHomotopyCategory_map_of_simplicialCylinder
    {X Y : PointedSimplicialPresheaf.{w} C}
    (h : parameterizedCylinder X (interval C) ⟶ Y) (i j : Fin 2) :
    (toStalkwiseHomotopyCategory C J).map (cylinderSection X (intervalEndpoint C i) ≫ h) =
      (toStalkwiseHomotopyCategory C J).map (cylinderSection X (intervalEndpoint C j) ≫ h) := by
  let Q := toStalkwiseHomotopyCategory C J
  let p := cylinderProjection X (interval C)
  have hp : IsIso (Q.map p) := isIso_toStalkwiseHomotopyCategory_map C p
    (stalkwiseWeakEquivalences_cylinderProjection_interval C J X)
  let e := @asIso _ _ _ _ (Q.map p) hp
  have hs : Q.map (cylinderSection X (intervalEndpoint C i)) =
      Q.map (cylinderSection X (intervalEndpoint C j)) := by
    apply (Iso.cancel_iso_hom_right _ _ e).1
    change Q.map (cylinderSection X (intervalEndpoint C i)) ≫ Q.map p =
      Q.map (cylinderSection X (intervalEndpoint C j)) ≫ Q.map p
    simp only [← Q.map_comp, p, cylinderSection_projection]
  simp only [Functor.map_comp]
  exact congrArg (· ≫ Q.map h) hs

end CategoryTheory.PointedSimplicialPresheaf
