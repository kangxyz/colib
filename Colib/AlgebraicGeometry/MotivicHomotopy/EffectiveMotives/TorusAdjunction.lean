/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.NisnevichReflection
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusRight
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedDerivedAdjunction
import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveExact
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The reduced torus adjunction on effective motives

The bounded-above projective tensor and the reduced total derived
torus sections give an adjunction after Nisnevich and A¹-localization.
The Hom correspondence is the one induced by the original split
projective tensor adjunction and the singular augmentation.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
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
local notation "NST" => LargeSheaves k
local notation "L" => projectiveReducedTorusTensorToDerivedMinus k
local notation "M" => effectiveReflection k
local notation "R" => effectiveReducedTorusSectionsFunctor k
local notation "I" => effectiveMotivesMinusInclusion k
local notation "J" => effectiveMotivesMinusToDerived k
local notation "a" => derivedNisnevichSheafification k
local notation "U" => forgetDerivedFunctor k
local notation "D" => DerivedCategory.Minus.ι

/-- The reduced projective torus tensor followed by the original localization. -/
abbrev projectiveEffectiveTorus : DerivedCategory.Minus PST ⥤ EffectiveMotivesMinus k :=
  L ⋙ M

private def toReducedForget (K : EffectiveMotivesMinus k) :
    (U).obj ((reducedTorusSectionsDerivedFunctor k).obj ((J).obj K)) ≅
      (U).obj ((J).obj ((R).obj K)) :=
  (U).mapIso ((effectiveReducedTorusSectionsToDerivedIso k).app K).symm

/-- The reduced projective Hom equivalence transported to effective targets. -/
def projectiveEffectiveTorusHomEquiv
    (P : DerivedCategory.Minus PST) (K : EffectiveMotivesMinus k) :
    ((projectiveEffectiveTorus k).obj P ⟶ K) ≃
      ((a).obj P ⟶ (I).obj ((R).obj K)) :=
  let e := (effectiveReflectionAdjunction k).homEquiv ((L).obj P) K
  let d : DerivedCategory.Minus NST ⥤ DerivedCategory NST := D
  let f := Functor.FullyFaithful.ofFullyFaithful d
  let f₁ := f.homEquiv (X := (L).obj P) (Y := (I).obj K)
  let f₂ := f.homEquiv (X := (a).obj P) (Y := (I).obj ((R).obj K))
  let h := projectiveReducedTorusTensorDerivedHomEquiv k P ((J).obj K)
  let g : (d.obj ((a).obj P) ⟶ d.obj ((I).obj ((R).obj K))) ≃
      (P.obj ⟶ (U).obj ((J).obj ((R).obj K))) :=
    (nisnevichDerivedAdjunction k).homEquiv P.obj ((J).obj ((R).obj K))
  e.trans (f₁.trans (h.trans ((toReducedForget k K).homToEquiv.trans
    (g.symm.trans f₂.symm))))

/-- Transposing a map from the projective tensor retains the original
derived projective transpose before reflecting the source. -/
theorem projectiveEffectiveTorusHomEquiv_map
    (P : DerivedCategory.Minus PST) (K : EffectiveMotivesMinus k)
    (g : (projectiveEffectiveTorus k).obj P ⟶ K) :
    (nisnevichDerivedAdjunction k).homEquiv P.obj ((J).obj ((R).obj K))
        ((D).map (projectiveEffectiveTorusHomEquiv k P K g)) =
      projectiveReducedTorusTensorDerivedHomEquiv k P ((J).obj K)
          ((D).map ((effectiveReflectionAdjunction k).homEquiv ((L).obj P) K g)) ≫
        (U).map ((effectiveReducedTorusSectionsToDerivedIso k).inv.app K) := by
  let e := (effectiveReflectionAdjunction k).homEquiv ((L).obj P) K
  let f := Functor.FullyFaithful.ofFullyFaithful
    (D : DerivedCategory.Minus NST ⥤ DerivedCategory NST)
  let h := projectiveReducedTorusTensorDerivedHomEquiv k P ((J).obj K)
  let b := (nisnevichDerivedAdjunction k).homEquiv P.obj ((J).obj ((R).obj K))
  let z := h ((D).map (e g)) ≫ (toReducedForget k K).hom
  let f' := f.homEquiv (X := (a).obj P) (Y := (I).obj ((R).obj K))
  change b (f' (f'.symm (b.symm z))) = z
  exact (congrArg b (f'.apply_symm_apply (b.symm z))).trans (b.apply_symm_apply z)

/-- The effective Hom comparison preserves the original coefficient maps. -/
theorem projectiveEffectiveTorusHomEquiv_postcompose
    (P : DerivedCategory.Minus PST) {K K' : EffectiveMotivesMinus k} (f : K ⟶ K')
    (g : (projectiveEffectiveTorus k).obj P ⟶ K) :
    projectiveEffectiveTorusHomEquiv k P K' (g ≫ f) =
      projectiveEffectiveTorusHomEquiv k P K g ≫ (I).map ((R).map f) := by
  let A := effectiveReflectionAdjunction k
  let B := nisnevichDerivedAdjunction k
  let d := (D : DerivedCategory.Minus NST ⥤ DerivedCategory NST)
  let b := B.homEquiv P.obj ((J).obj ((R).obj K'))
  let d' := (Functor.FullyFaithful.ofFullyFaithful d).homEquiv
    (X := (a).obj P) (Y := (I).obj ((R).obj K'))
  let e := effectiveReducedTorusSectionsToDerivedIso k
  let c := (U)
  have hg : d.map (projectiveEffectiveTorusHomEquiv k P K g ≫ (I).map ((R).map f)) =
      d.map (projectiveEffectiveTorusHomEquiv k P K g) ≫ (J).map ((R).map f) :=
    d.map_comp _ _
  have hr : (toReducedForget k K).hom ≫ c.map ((J).map ((R).map f)) =
      c.map ((reducedTorusSectionsDerivedFunctor k).map ((J).map f)) ≫
        (toReducedForget k K').hom := by
    change c.map (e.inv.app K) ≫ c.map ((J).map ((R).map f)) =
      c.map ((reducedTorusSectionsDerivedFunctor k).map ((J).map f)) ≫ c.map (e.inv.app K')
    exact (c.map_comp _ _).symm.trans
      ((c.congr_map (e.inv.naturality f).symm).trans (c.map_comp _ _))
  apply (d'.trans b).injective
  change b (d.map (projectiveEffectiveTorusHomEquiv k P K' (g ≫ f))) =
    b (d.map (projectiveEffectiveTorusHomEquiv k P K g ≫ (I).map ((R).map f)))
  have hn : (A.homEquiv ((L).obj P) K') (g ≫ f) =
      (A.homEquiv ((L).obj P) K) g ≫ (I).map f :=
    A.homEquiv_naturality_right g f
  have hd : d.map ((A.homEquiv ((L).obj P) K') (g ≫ f)) =
      d.map ((A.homEquiv ((L).obj P) K) g) ≫ (J).map f :=
    (d.congr_map hn).trans (d.map_comp _ _)
  have hg' := (congrArg b hg).trans
    (B.homEquiv_naturality_right (d.map (projectiveEffectiveTorusHomEquiv k P K g))
      ((J).map ((R).map f)))
  have h₁ := projectiveEffectiveTorusHomEquiv_map k P K' (g ≫ f)
  have h₂ := projectiveEffectiveTorusHomEquiv_map k P K g
  let q := projectiveReducedTorusTensorDerivedHomEquiv k P ((J).obj K)
    (d.map ((A.homEquiv ((L).obj P) K) g))
  let m := c.map ((reducedTorusSectionsDerivedFunctor k).map ((J).map f))
  calc
    _ = (q ≫ m) ≫ (toReducedForget k K').hom := by
      refine h₁.trans ?_
      rw [hd, projectiveReducedTorusTensorDerivedHomEquiv_postcompose]
      rfl
    _ = (q ≫ (toReducedForget k K).hom) ≫ c.map ((J).map ((R).map f)) :=
      (Category.assoc _ _ _).trans
        ((congrArg (q ≫ ·) hr.symm).trans (Category.assoc _ _ _).symm)
    _ = _ := (congrArg (· ≫ c.map ((J).map ((R).map f))) h₂.symm).trans hg'.symm

private def reflectionTorusHomEquiv (P : DerivedCategory.Minus NST) (K : EffectiveMotivesMinus k) :
    ((projectiveEffectiveTorus k).obj (presheafLift k P) ⟶ K) ≃
      ((M).obj P ⟶ (R).obj K) :=
  (projectiveEffectiveTorusHomEquiv k (presheafLift k P) K).trans
    ((sheafificationPresheafLiftIso k P).homFromEquiv.trans
      ((effectiveReflectionAdjunction k).homEquiv P ((R).obj K)).symm)

private theorem reflectionTorusHomEquiv_postcompose
    (P : DerivedCategory.Minus NST) {K K' : EffectiveMotivesMinus k}
    (f : K ⟶ K') (g : (projectiveEffectiveTorus k).obj (presheafLift k P) ⟶ K) :
    reflectionTorusHomEquiv k P K' (g ≫ f) =
      reflectionTorusHomEquiv k P K g ≫ (R).map f := by
  let B := effectiveReflectionAdjunction k
  apply (B.homEquiv P ((R).obj K')).injective
  let h := (B.homEquiv P ((R).obj K'))
  let h' := (B.homEquiv P ((R).obj K))
  let e := (sheafificationPresheafLiftIso k P).homFromEquiv
    (Z := (I).obj ((R).obj K))
  let e' := (sheafificationPresheafLiftIso k P).homFromEquiv
    (Z := (I).obj ((R).obj K'))
  let t := projectiveEffectiveTorusHomEquiv k (presheafLift k P) K g
  let t' := projectiveEffectiveTorusHomEquiv k (presheafLift k P) K' (g ≫ f)
  change h (h.symm (e' t')) = h (h'.symm (e t) ≫ (R).map f)
  calc
    _ = e' t' := h.apply_symm_apply _
    _ = e' (t ≫ (I).map ((R).map f)) :=
      congrArg e' (projectiveEffectiveTorusHomEquiv_postcompose k (presheafLift k P) f g)
    _ = (e t) ≫ (I).map ((R).map f) := by
      change (sheafificationPresheafLiftIso k P).inv ≫ t ≫ (I).map ((R).map f) =
        ((sheafificationPresheafLiftIso k P).inv ≫ t) ≫ (I).map ((R).map f)
      exact (Category.assoc _ _ _).symm
    _ = _ := ((B.homEquiv_naturality_right (h'.symm (e t)) ((R).map f)).trans
      (congrArg (· ≫ (I).map ((R).map f)) (h'.apply_symm_apply (e t)))).symm

private def effectiveTorusHomEquiv (K T : EffectiveMotivesMinus k) :
    ((projectiveEffectiveTorus k).obj (presheafLift k K.obj) ⟶ T) ≃ (K ⟶ (R).obj T) :=
  (reflectionTorusHomEquiv k K.obj T).trans
    ((asIso ((effectiveReflectionAdjunction k).counit.app K)).homFromEquiv)

private theorem effectiveTorusHomEquiv_postcompose (K : EffectiveMotivesMinus k)
    {T T' : EffectiveMotivesMinus k} (f : T ⟶ T')
    (g : (projectiveEffectiveTorus k).obj (presheafLift k K.obj) ⟶ T) :
    effectiveTorusHomEquiv k K T' (g ≫ f) =
      effectiveTorusHomEquiv k K T g ≫ (R).map f := by
  let i := (asIso ((effectiveReflectionAdjunction k).counit.app K)).inv
  let t := reflectionTorusHomEquiv k K.obj T g
  let t' := reflectionTorusHomEquiv k K.obj T' (g ≫ f)
  change i ≫ t' = (i ≫ t) ≫ (R).map f
  exact (congrArg (i ≫ ·) (reflectionTorusHomEquiv_postcompose k K.obj f g)).trans
    (Category.assoc i t ((R).map f)).symm

/-- The derived reduced torus tensor on the original effective category. -/
def effectiveReducedTorusTensorFunctor : EffectiveMotivesMinus k ⥤ EffectiveMotivesMinus k :=
  Adjunction.leftAdjointOfEquiv (effectiveTorusHomEquiv k) (fun K _ _ =>
    effectiveTorusHomEquiv_postcompose k K)

/-- The actual effective tensor and reduced torus sections are adjoint. -/
def effectiveReducedTorusTensorAdjunction :
    effectiveReducedTorusTensorFunctor k ⊣ R :=
  Adjunction.adjunctionOfEquivLeft (effectiveTorusHomEquiv k) (fun K _ _ =>
    effectiveTorusHomEquiv_postcompose k K)

/-- The effective reduced tensor is computed on any bounded-above
presheaf representative, via the same Hom comparison. -/
def projectiveEffectiveTorusComparison (P : DerivedCategory.Minus PST) :
    (projectiveEffectiveTorus k).obj P ≅
      ((a ⋙ M) ⋙ effectiveReducedTorusTensorFunctor k).obj P := by
  let X := (projectiveEffectiveTorus k).obj P
  let Y := ((a ⋙ M) ⋙ effectiveReducedTorusTensorFunctor k).obj P
  let A := effectiveReflectionAdjunction k
  let B := effectiveReducedTorusTensorAdjunction k
  let e (K : EffectiveMotivesMinus k) : (X ⟶ K) ≃ (Y ⟶ K) :=
    (projectiveEffectiveTorusHomEquiv k P K).trans
      (((A.homEquiv ((a).obj P) ((R).obj K)).symm).trans
        ((B.homEquiv ((M).obj ((a).obj P)) K).symm))
  have h (K K' : EffectiveMotivesMinus k) (f : K ⟶ K') (g : X ⟶ K) :
      e K' (g ≫ f) = e K g ≫ f := by
    let b := B.homEquiv ((M).obj ((a).obj P)) K
    let b' := B.homEquiv ((M).obj ((a).obj P)) K'
    let a₀ := A.homEquiv ((a).obj P) ((R).obj K)
    let a₀' := A.homEquiv ((a).obj P) ((R).obj K')
    let t := projectiveEffectiveTorusHomEquiv k P K g
    let t' := projectiveEffectiveTorusHomEquiv k P K' (g ≫ f)
    apply b'.injective
    change b' (b'.symm (a₀'.symm t')) = b' (b.symm (a₀.symm t) ≫ f)
    calc
      _ = a₀'.symm t' := b'.apply_symm_apply _
      _ = a₀.symm t ≫ (R).map f := by
        apply a₀'.injective
        calc
          a₀' (a₀'.symm t') = t' := a₀'.apply_symm_apply t'
          _ = t ≫ (I).map ((R).map f) := projectiveEffectiveTorusHomEquiv_postcompose k P f g
          _ = a₀' (a₀.symm t ≫ (R).map f) :=
            ((A.homEquiv_naturality_right (a₀.symm t) ((R).map f)).trans
              (congrArg (· ≫ (I).map ((R).map f)) (a₀.apply_symm_apply t))).symm
      _ = _ := ((B.homEquiv_naturality_right (b.symm (a₀.symm t)) f).trans
        (congrArg (· ≫ (R).map f) (b.apply_symm_apply (a₀.symm t)))).symm
  refine
    { hom := (e Y).symm (𝟙 Y)
      inv := e X (𝟙 X)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply (e X).injective
    rw [h, Equiv.apply_symm_apply, Category.id_comp]
  · rw [← h, Category.id_comp, Equiv.apply_symm_apply]

/-- The projective comparison identifies the actual effective unit with
the projective Hom transpose after the original localization map. -/
theorem projectiveEffectiveTorusComparison_hom_unit (P : DerivedCategory.Minus PST) :
    projectiveEffectiveTorusHomEquiv k P
        ((effectiveReducedTorusTensorFunctor k).obj ((M).obj ((a).obj P)))
        (projectiveEffectiveTorusComparison k P).hom =
      (effectiveReflectionAdjunction k).unit.app ((a).obj P) ≫
        (I).map ((effectiveReducedTorusTensorAdjunction k).unit.app ((M).obj ((a).obj P))) := by
  let X := (projectiveEffectiveTorus k).obj P
  let Y := (effectiveReducedTorusTensorFunctor k).obj ((M).obj ((a).obj P))
  let A := effectiveReflectionAdjunction k
  let B := effectiveReducedTorusTensorAdjunction k
  let aP := (a).obj P
  let e : (X ⟶ Y) ≃ (Y ⟶ Y) :=
    (projectiveEffectiveTorusHomEquiv k P Y).trans
      ((A.homEquiv aP ((R).obj Y)).symm.trans ((B.homEquiv ((M).obj aP) Y).symm))
  have h : e ((projectiveEffectiveTorusComparison k P).hom) = 𝟙 Y :=
    e.apply_symm_apply _
  let b := B.homEquiv ((M).obj aP) Y
  let a₀ := A.homEquiv aP ((R).obj Y)
  let t := projectiveEffectiveTorusHomEquiv k P Y (projectiveEffectiveTorusComparison k P).hom
  change b.symm (a₀.symm t) = 𝟙 Y at h
  calc
    t = a₀ (a₀.symm t) := (a₀.apply_symm_apply t).symm
    _ = a₀ (b (b.symm (a₀.symm t))) :=
      congrArg a₀ (b.apply_symm_apply _).symm
    _ = a₀ (b (𝟙 Y)) := congrArg (fun m => a₀ (b m)) h
    _ = a₀ (B.unit.app ((M).obj aP)) := congrArg a₀ (B.homEquiv_id _)
    _ = _ := A.homEquiv_unit aP ((R).obj Y) (B.unit.app ((M).obj aP))

/-- The effective reduced tensor preserves upper bounds. -/
theorem effectiveReducedTorusTensor_isLE
    (K : EffectiveMotivesMinus k) (b : ℤ) (hK : ((J).obj K).IsLE b) :
    ((J).obj ((effectiveReducedTorusTensorFunctor k).obj K)).IsLE b := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_presheafLift_of_isLE k K.obj b hK
  let F := effectiveReducedTorusTensorFunctor k
  let E := effectiveReflectionAdjunction k
  let d := projectiveEffectiveTorusComparison k P ≪≫
    F.mapIso ((M).mapIso e ≪≫ asIso (E.counit.app K))
  let H := effectiveMotivesMinusToDerived k
  let : (H.obj ((projectiveEffectiveTorus k).obj P)).IsLE b :=
    effectiveReflection_isLE k ((L).obj P) b
      (projectiveReducedTorusTensorToDerivedMinus_isLE k P b hP)
  exact DerivedCategory.TStructure.t.isLE_of_iso (H.mapIso d) b

end AlgebraicGeometry.MotivicHomotopy
