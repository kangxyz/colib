/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Exactness
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Representable
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.RepresentableTorusUnit
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SingleReflection
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusRightCoproducts
import Colib.Util.References
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.NisnevichSingleCoproduct
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.GeneratorDevissage
import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveExact
import Mathlib.CategoryTheory.Adjunction.Limits
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Cancellation on bounded-above effective motives

The natural unit is tested after the original sheafification and
effective reflection from bounded-above presheaves. Invertibility
on smooth motives extends to direct sums, to projective retracts,
and then through finite windows in a bounded-above projective complex.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "M" => derivedNisnevichSheafification k ⋙ effectiveReflection k
local notation "E" => effectiveMotivesMinusToDerived k
local notation "L" => effectiveReducedTorusTensorFunctor k
local notation "R" => effectiveReducedTorusSectionsFunctor k
set_option quotPrecheck false in
local notation "η" => (effectiveReducedTorusTensorAdjunction k).unit

local instance : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

private abbrev generatorFamily {I : Type (u + 1)} (X : I → Cor k) (n : ℤ) :
    I → DerivedCategory.Minus PST :=
  fun i => (singleDerivedMinus k n).obj ((representableLarge k).obj (X i))

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
private theorem effectiveFromPresheaf_isLE (P : DerivedCategory.Minus PST) (b : ℤ)
    (hP : P.obj.IsLE b) : ((E).obj ((M).obj P)).IsLE b := by
  let a := nisnevichSheafify k
  let : P.obj.IsLE b := hP
  apply effectiveReflection_isLE k _ b
  change (a.mapDerivedCategory.obj P.obj).IsLE b
  apply (DerivedCategory.isLE_iff _ b).2
  intro n hn
  exact (a.map_isZero (DerivedCategory.isZero_of_isLE P.obj b n hn)).of_iso
    ((a.mapDerivedCategoryHomologyIso n).app P.obj)

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
private theorem effectiveFromPresheaf_preservesColimit {I : Type (u + 1)}
    (X : I → Cor k) (n : ℤ) :
    PreservesColimit (Discrete.functor (generatorFamily k X n)) (M) := by
  let P := fun i => (representableLarge k).obj (X i)
  let : PreservesColimit (Discrete.functor (generatorFamily k X n))
      (derivedNisnevichSheafification k) :=
    derivedNisnevichSheafification_preservesColimit_single k P n
  let : (effectiveReflection k).IsLeftAdjoint := (effectiveReflectionAdjunction k).isLeftAdjoint
  let : PreservesColimit (Discrete.functor (generatorFamily k X n) ⋙
      derivedNisnevichSheafification k) (effectiveReflection k) := inferInstance
  exact comp_preservesColimit (derivedNisnevichSheafification k) (effectiveReflection k)

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem effectiveInclusion_preservesColimit_of_bound {I : Type (u + 1)}
    (K : I → EffectiveMotivesMinus k) (b : ℤ)
    (hK : ∀ i, ((E).obj (K i)).IsLE b) : PreservesColimit (Discrete.functor K) (E) := by
  let V := (E)
  let W := fun i => V.obj (K i)
  let A := SheafWithTransfers.{u + 1} k
  let : HasCoproductsOfShape I (DerivedCategory A) :=
    Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory A I
  refine preservesColimit_of_preserves_colimit_cocone (effectiveCofanIsColimit k K b hK) ?_
  let d : Discrete.functor K ⋙ V ≅ Discrete.functor W :=
    Discrete.natIso (fun _ => Iso.refl _)
  let t : IsColimit (Cofan.mk (∐ W) (Sigma.ι W)) := coproductIsCoproduct W
  refine ((IsColimit.precomposeHomEquiv d _).symm t).ofIsoColimit ?_
  refine Cocone.ext (Iso.refl _) (fun i => ?_)
  unfold effectiveCofan
  change (𝟙 _ ≫ Sigma.ι W i.as) ≫ 𝟙 _ = Sigma.ι W i.as
  rw [Category.id_comp, Category.comp_id]

private abbrev unitAfterReflection :
    M ⋙ E ⟶ (M ⋙ (L ⋙ R)) ⋙ E :=
  Functor.whiskerRight
    ((Functor.rightUnitor (M)).inv ≫ Functor.whiskerLeft (M) (η)) (E)

private theorem isIso_unitAfterReflection_single
    (h : ∀ Y : Cor k, IsIso ((η).app ((effectiveMotive k).obj Y))) (Y : Cor k) (n : ℤ)
    (e : ((M).obj ((singleDerivedMinus k 0).obj ((representableLarge k).obj Y))) ≅
      (effectiveMotive k).obj Y) :
    IsIso ((unitAfterReflection k).app
      ((singleDerivedMinus k n).obj ((representableLarge k).obj Y))) := by
  let P := (representableLarge k).obj Y
  let X := (singleDerivedMinus k 0).obj P
  let X' := (singleDerivedMinus k n).obj P
  let v : DerivedCategory.Minus PST ⥤ DerivedCategory PST := DerivedCategory.Minus.ι
  let d₀ : v.obj X ≅ (DerivedCategory.singleFunctor PST 0).obj P :=
    ((DerivedCategory.singleFunctorIsoCompQ PST 0).app P).symm
  let d₁ : (DerivedCategory.singleFunctor PST n).obj P ≅ v.obj X' :=
    (DerivedCategory.singleFunctorIsoCompQ PST n).app P
  let dShift :
      (shiftFunctor (DerivedCategory PST) (-n)).obj ((DerivedCategory.singleFunctor PST 0).obj P) ≅
        (DerivedCategory.singleFunctor PST n).obj P :=
    ((DerivedCategory.singleFunctors PST).shiftIso (-n) n 0 (by omega)).app P
  let d : v.obj (X⟦-n⟧) ≅ v.obj X' :=
    (v.commShiftIso (-n)).app X ≪≫ (shiftFunctor _ (-n)).mapIso d₀ ≪≫ dShift ≪≫ d₁
  let : (derivedNisnevichSheafification k).CommShift ℤ := inferInstanceAs
    (((nisnevichSheafify k).mapDerivedCategoryMinus).CommShift ℤ)
  let d' := (Functor.FullyFaithful.ofFullyFaithful v).preimageIso d
  let e' := ((M).commShiftIso (-n)).app X ≪≫ (shiftFunctor _ (-n)).mapIso e
  let : IsIso ((η).app ((effectiveMotive k).obj Y)) := h Y
  let A := effectiveReducedTorusTensorAdjunction k
  have hr : IsIso (A.unit.app (((effectiveMotive k).obj Y)⟦-n⟧)) := by
    rw [← A.unit_app_shift_commShiftIso_inv_app]
    infer_instance
  have hh := (A.unit.isIso_app_iff_of_iso ((M).mapIso d').symm).2
    ((A.unit.isIso_app_iff_of_iso e').2 hr)
  let : IsIso (A.unit.app ((M).obj X')) := hh
  change IsIso ((E).map (𝟙 _ ≫ A.unit.app ((M).obj X')))
  rw [Category.id_comp]
  infer_instance

/-- A unit comparison on the original smooth motives suffices for
the actual effective reduced torus adjunction. -/
theorem isIso_effectiveReducedTorusTensor_unit_of_representables
    (h : ∀ Y : Cor k, IsIso ((η).app ((effectiveMotive k).obj Y)))
    (h₀ : ∀ Y : Cor k,
      Nonempty (((M).obj ((singleDerivedMinus k 0).obj ((representableLarge k).obj Y))) ≅
        (effectiveMotive k).obj Y))
    (K : EffectiveMotivesMinus k) : IsIso ((η).app K) := by
  let F := (M) ⋙ (E)
  let G := ((M) ⋙ ((L) ⋙ (R))) ⋙ (E)
  let A := effectiveReducedTorusTensorAdjunction k
  let H := effectiveReflectionAdjunction k
  let : (L).IsLeftAdjoint := A.isLeftAdjoint
  let : (derivedNisnevichSheafification k).CommShift ℤ := inferInstanceAs
    (((nisnevichSheafify k).mapDerivedCategoryMinus).CommShift ℤ)
  let : (derivedNisnevichSheafification k).IsTriangulated := nisnevichDerivedMinus_isTriangulated k
  let : (M).CommShift ℤ := inferInstance
  let : (M).IsTriangulated := inferInstance
  have hFsum (I : Type (u + 1)) (X : I → Cor k) (n : ℤ) :
      PreservesColimit (Discrete.functor (generatorFamily k X n)) F := by
    let P := generatorFamily k X n
    let : PreservesColimit (Discrete.functor P) (M) :=
      effectiveFromPresheaf_preservesColimit k X n
    let Q := fun i => (M).obj (P i)
    let d : Discrete.functor P ⋙ (M) ≅ Discrete.functor Q :=
      Discrete.natIso (fun _ => Iso.refl _)
    let hQ (i : I) : ((E).obj (Q i)).IsLE n :=
      effectiveFromPresheaf_isLE k (P i) n
        (inferInstanceAs ((DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor PST n).obj ((representableLarge k).obj (X i)))).IsLE n))
    let : PreservesColimit (Discrete.functor Q) (E) :=
      effectiveInclusion_preservesColimit_of_bound k Q n hQ
    let : PreservesColimit (Discrete.functor P ⋙ (M)) (E) :=
      preservesColimit_of_iso_diagram (E) d.symm
    exact comp_preservesColimit (M) (E)
  have hGsum (I : Type (u + 1)) (X : I → Cor k) (n : ℤ) :
      PreservesColimit (Discrete.functor (generatorFamily k X n)) G := by
    let P := generatorFamily k X n
    let Q := fun i => ((M) ⋙ (L)).obj (P i)
    let W := fun i => (R).obj (Q i)
    let : PreservesColimit (Discrete.functor P) (M) :=
      effectiveFromPresheaf_preservesColimit k X n
    let : PreservesColimit (Discrete.functor P ⋙ (M)) (L) := inferInstance
    let : PreservesColimit (Discrete.functor P) ((M) ⋙ (L)) := comp_preservesColimit (M) (L)
    let d : Discrete.functor P ⋙ ((M) ⋙ (L)) ≅ Discrete.functor Q :=
      Discrete.natIso (fun _ => Iso.refl _)
    let e : Discrete.functor Q ⋙ (R) ≅ Discrete.functor W :=
      Discrete.natIso (fun _ => Iso.refl _)
    let hQ (i : I) : ((E).obj (Q i)).IsLE n :=
      effectiveReducedTorusTensor_isLE k _ n
        (effectiveFromPresheaf_isLE k (P i) n
          (inferInstanceAs ((DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor PST n).obj ((representableLarge k).obj (X i)))).IsLE n)))
    let hW (i : I) : ((E).obj (W i)).IsLE n := by
      let : ((E).obj (Q i)).IsLE n := hQ i
      exact reducedTorusSectionsDerived_isLE_of_isLE_of_isA1Invariant k _ n (Q i).property
    let : PreservesColimit (Discrete.functor Q) (R) :=
      effectiveReducedTorusSections_preservesColimit k Q n hQ
    let : PreservesColimit (Discrete.functor W) (E) :=
      effectiveInclusion_preservesColimit_of_bound k W n hW
    let : PreservesColimit (Discrete.functor Q ⋙ (R)) (E) :=
      preservesColimit_of_iso_diagram (E) e.symm
    let : PreservesColimit (Discrete.functor Q) ((R) ⋙ (E)) := inferInstance
    let : PreservesColimit (Discrete.functor P ⋙ ((M) ⋙ (L))) ((R) ⋙ (E)) :=
      preservesColimit_of_iso_diagram ((R) ⋙ (E)) d.symm
    let F' := ((M) ⋙ (L)) ⋙ (R) ⋙ (E)
    let : PreservesColimit (Discrete.functor P) F' := comp_preservesColimit ((M) ⋙ (L)) ((R) ⋙ (E))
    let a : F' ≅ G := (Functor.associator ((M) ⋙ (L)) (R) (E)).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator (M) (L) (R)) (E)
    exact preservesColimit_of_natIso _ a
  have hF (P : DerivedCategory.Minus PST) (b : ℤ) (hP : P.obj.IsLE b) :
      (F.obj P).IsLE (b + 0) := by
    rw [add_zero]
    exact effectiveFromPresheaf_isLE k P b hP
  have hG (P : DerivedCategory.Minus PST) (b : ℤ) (hP : P.obj.IsLE b) :
      (G.obj P).IsLE (b + 0) := by
    let Y := (L).obj ((M).obj P)
    let : ((E).obj Y).IsLE b := effectiveReducedTorusTensor_isLE k _ b
      (effectiveFromPresheaf_isLE k P b hP)
    let : ((E ⋙ reducedTorusSectionsDerivedFunctor k).obj Y).IsLE b :=
      reducedTorusSectionsDerived_isLE_of_isLE_of_isA1Invariant k ((E).obj Y) b Y.property
    rw [add_zero]
    exact DerivedCategory.TStructure.t.isLE_of_iso
      ((effectiveReducedTorusSectionsToDerivedIso k).app Y).symm b
  let P := presheafLift k K.obj
  let e : (M).obj P ≅ K :=
    (effectiveReflection k).mapIso (sheafificationPresheafLiftIso k K.obj) ≪≫
      asIso (H.counit.app K)
  have hp : IsIso ((unitAfterReflection k).app P) :=
    isIso_app_of_isIso_singleDerivedMinus_representable k (unitAfterReflection k)
      (fun Y n => isIso_unitAfterReflection_single k h Y n (h₀ Y).some)
      hFsum hGsum 0 hF hG P
  change IsIso ((E).map (𝟙 _ ≫ (η).app ((M).obj P))) at hp
  rw [Category.id_comp] at hp
  let : IsIso ((E).map ((η).app ((M).obj P))) := hp
  let V : EffectiveMotivesMinus k ⥤ DerivedCategory (LargeSheaves k) := E
  let : V.Full := inferInstanceAs
    (((effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι).Full)
  let : V.Faithful := inferInstanceAs
    (((effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι).Faithful)
  exact ((η).isIso_app_iff_of_iso e).1 (isIso_of_reflects_iso _ V)

/-- The unit of the original reduced torus adjunction is invertible
on every bounded-above effective motive. -/
theorem isIso_effectiveReducedTorusTensorAdjunction_unit_app (K : EffectiveMotivesMinus k) :
    IsIso ((η).app K) :=
  isIso_effectiveReducedTorusTensor_unit_of_representables k
    (isIso_effectiveReducedTorusTensorAdjunction_unit_app_representable k)
    (fun Y => ⟨singleEffectiveReflectionIso k ((representableLarge k).obj Y)⟩) K

instance : IsIso (η) :=
  let _ : ∀ K, IsIso ((η).app K) := isIso_effectiveReducedTorusTensorAdjunction_unit_app k
  NatIso.isIso_of_isIso_app (η)

/-- Voevodsky cancellation on the original bounded-above effective
category, for the tensor with the reduced multiplicative group. -/
@[colib_ref "Voevodsky2010Cancellation" "Corollary 4.10, p. 684" "ingredient"
  "Full faithfulness for the reduced torus before the Tate shift"]
def effectiveReducedTorusTensorFullyFaithful : (L).FullyFaithful :=
  (effectiveReducedTorusTensorAdjunction k).fullyFaithfulLOfIsIsoUnit

end AlgebraicGeometry.MotivicHomotopy
