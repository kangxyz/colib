/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Exactness
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.AdjunctionShift
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveExact

/-! # Naturality of the original projective reduced torus comparison -/

@[expose] public noncomputable section

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
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "a(" K ")" => derivedNisnevichSheafification K
local notation "i(" K ")" => effectiveMotivesMinusInclusion K
local notation "j(" K ")" => effectiveMotivesMinusToDerived K
local notation "M(" K ")" => effectiveReflection K
local notation "L(" K ")" => projectiveReducedTorusTensorToDerivedMinus K
local notation "R(" K ")" => effectiveReducedTorusSectionsFunctor K
local notation "T(" K ")" => effectiveReducedTorusTensorFunctor K

private theorem projectiveEffectiveTorusHomEquiv_precompose
    {P P' : DerivedCategory.Minus PST(k)} (K : EffectiveMotivesMinus k) (f : P' ⟶ P)
    (g : (projectiveEffectiveTorus k).obj P ⟶ K) :
    projectiveEffectiveTorusHomEquiv k P' K ((projectiveEffectiveTorus k).map f ≫ g) =
      (a(k)).map f ≫ projectiveEffectiveTorusHomEquiv k P K g := by
  let d := DerivedCategory.Minus.ι (C := NST(k))
  let A := effectiveReflectionAdjunction k
  let B := nisnevichDerivedAdjunction k
  let g' := A.homEquiv ((L(k)).obj P) K g
  let Z := (j(k)).obj ((R(k)).obj K)
  let θ := B.homEquiv P'.obj Z
  apply (d.map_injective)
  apply θ.injective
  -- Compare the same two transposes under the ordinary derived sheafification adjunction.
  have h₀ : A.homEquiv ((L(k)).obj P') K ((projectiveEffectiveTorus k).map f ≫ g) =
      (L(k)).map f ≫ g' := A.homEquiv_naturality_left ((L(k)).map f) g
  have h₁ : d.map (A.homEquiv ((L(k)).obj P') K ((projectiveEffectiveTorus k).map f ≫ g)) =
      d.map ((L(k)).map f) ≫ d.map g' := by rw [h₀, d.map_comp]
  have h₂ : θ (d.map ((a(k)).map f ≫ projectiveEffectiveTorusHomEquiv k P K g)) =
      f.hom ≫ (B.homEquiv P.obj Z) (d.map (projectiveEffectiveTorusHomEquiv k P K g)) := by
    rw [d.map_comp]
    exact B.homEquiv_naturality_left f.hom _
  change θ (d.map (projectiveEffectiveTorusHomEquiv k P' K
    ((projectiveEffectiveTorus k).map f ≫ g))) = _
  rw [projectiveEffectiveTorusHomEquiv_map, h₂, projectiveEffectiveTorusHomEquiv_map, h₁]
  have h₃ := projectiveReducedTorusTensorDerivedHomEquiv_precompose k ((j(k)).obj K) f (d.map g')
  change projectiveReducedTorusTensorDerivedHomEquiv k P' ((j(k)).obj K)
      (d.map ((L(k)).map f) ≫ d.map g') =
    f.hom ≫ projectiveReducedTorusTensorDerivedHomEquiv k P ((j(k)).obj K) (d.map g') at h₃
  rw [h₃, Category.assoc]

/-- The existing projective reduced torus comparisons form a natural
isomorphism on all bounded-above presheaf complexes. -/
def projectiveEffectiveTorusNatIso :
    projectiveEffectiveTorus k ≅ ((a(k) ⋙ M(k)) ⋙ T(k)) :=
  NatIso.ofComponents (projectiveEffectiveTorusComparison k) (by
    intro P Q f
    let A := effectiveReflectionAdjunction k
    let B := effectiveReducedTorusTensorAdjunction k
    let C := a(k) ⋙ M(k)
    let E := C ⋙ T(k)
    let I := i(k)
    let b := projectiveEffectiveTorusHomEquiv k P (E.obj Q)
    change (projectiveEffectiveTorus k).map f ≫ (projectiveEffectiveTorusComparison k Q).hom =
      (projectiveEffectiveTorusComparison k P).hom ≫ E.map f
    apply b.injective
    rw [projectiveEffectiveTorusHomEquiv_precompose, projectiveEffectiveTorusHomEquiv_postcompose]
    have hQ := projectiveEffectiveTorusComparison_hom_unit k Q
    have hP := projectiveEffectiveTorusComparison_hom_unit k P
    change projectiveEffectiveTorusHomEquiv k Q (E.obj Q)
      (projectiveEffectiveTorusComparison k Q).hom = _ at hQ
    change projectiveEffectiveTorusHomEquiv k P (E.obj P)
      (projectiveEffectiveTorusComparison k P).hom = _ at hP
    rw [hQ, hP]
    have hA := A.unit.naturality ((a(k)).map f)
    have hB := B.unit.naturality (C.map f)
    change (a(k)).map f ≫ A.unit.app ((a(k)).obj Q) =
      A.unit.app ((a(k)).obj P) ≫ I.map (C.map f) at hA
    change C.map f ≫ B.unit.app (C.obj Q) =
      B.unit.app (C.obj P) ≫ (R(k)).map ((T(k)).map (C.map f)) at hB
    change (a(k)).map f ≫ A.unit.app ((a(k)).obj Q) ≫ I.map (B.unit.app (C.obj Q)) =
      (A.unit.app ((a(k)).obj P) ≫ I.map (B.unit.app (C.obj P))) ≫
        I.map ((R(k)).map ((T(k)).map (C.map f)))
    calc
      _ = A.unit.app ((a(k)).obj P) ≫ I.map (C.map f ≫ B.unit.app (C.obj Q)) := by
        rw [← Category.assoc, hA, Category.assoc, I.map_comp]
      _ = _ := by rw [hB, I.map_comp, Category.assoc])

set_option maxHeartbeats 650000 in
-- The unit and transpose maps lie in the original bounded-above derived categories.
/-- The comparison from projective models to the original torus tensor preserves shift
when the original projective Hom bijection preserves shifted transposes. -/
theorem projectiveEffectiveTorusNatIso_commShift_of_homEquiv
    (h : ∀ (P : DerivedCategory.Minus PST(k)) (K : EffectiveMotivesMinus k)
      (g : (projectiveEffectiveTorus k).obj P ⟶ K) (n : ℤ),
      projectiveEffectiveTorusHomEquiv k (P⟦n⟧) (K⟦n⟧)
          (((projectiveEffectiveTorus k).commShiftIso n).hom.app P ≫ g⟦n⟧') ≫
          (((R(k)) ⋙ i(k)).commShiftIso n).hom.app K =
        (((a(k)).commShiftIso n).hom.app P) ≫
          (projectiveEffectiveTorusHomEquiv k P K g)⟦n⟧') :
    NatTrans.CommShift (projectiveEffectiveTorusNatIso k).hom ℤ := by
  let A := effectiveReflectionAdjunction k
  let B := effectiveReducedTorusTensorAdjunction k
  let C := a(k) ⋙ M(k)
  let F := projectiveEffectiveTorus k
  let G := C ⋙ T(k)
  let H := R(k) ⋙ i(k)
  let η := projectiveEffectiveTorusNatIso k
  let D := A.comp B
  let : D.CommShift ℤ := inferInstanceAs ((A.comp B).CommShift ℤ)
  refine ⟨fun n => NatTrans.ext (funext fun P => ?_)⟩
  change (F.commShiftIso n).hom.app P ≫ (η.hom.app P)⟦n⟧' =
    η.hom.app (P⟦n⟧) ≫ (G.commShiftIso n).hom.app P
  let P₀ := P⟦n⟧
  let K := G.obj P
  let f := (G.commShiftIso n).hom.app P
  let α := ((a(k)).commShiftIso n).hom.app P
  let e := (H.commShiftIso n).app K
  let x := (F.commShiftIso n).hom.app P ≫ (η.hom.app P)⟦n⟧'
  let y := η.hom.app P₀ ≫ f
  let φ := projectiveEffectiveTorusHomEquiv k P₀ (K⟦n⟧)
  change x = y
  apply φ.injective
  suffices hh : φ x ≫ e.hom = φ y ≫ e.hom by
    calc
      φ x = (φ x ≫ e.hom) ≫ e.inv := by
        exact ((Category.assoc _ _ _).trans
          ((congrArg (φ x ≫ ·) e.hom_inv_id).trans (Category.comp_id (φ x)))).symm
      _ = (φ y ≫ e.hom) ≫ e.inv := congrArg (· ≫ e.inv) hh
      _ = φ y := (Category.assoc _ _ _).trans
        ((congrArg (φ y ≫ ·) e.hom_inv_id).trans (Category.comp_id (φ y)))
  let aP := (a(k)).obj P
  let aP₀ := (a(k)).obj P₀
  have hP (X : DerivedCategory.Minus PST(k)) :
      projectiveEffectiveTorusHomEquiv k X (G.obj X) (η.hom.app X) =
        D.unit.app ((a(k)).obj X) := by
    rw [Adjunction.comp_unit_app]
    exact projectiveEffectiveTorusComparison_hom_unit k X
  have h₁ : φ x ≫ e.hom = α ≫ (D.unit.app aP)⟦n⟧' := by
    exact (h P K (η.hom.app P) n).trans
      (congrArg (fun z => α ≫ z⟦n⟧') (hP P))
  let b₁ := ((M(k) ⋙ T(k)).commShiftIso n).hom.app aP
  have h₂ : (D.unit.app aP)⟦n⟧' = D.unit.app (aP⟦n⟧) ≫ H.map b₁ ≫ e.hom :=
    D.shift_unit_app n aP
  have h₃ : α ≫ D.unit.app (aP⟦n⟧) =
      D.unit.app aP₀ ≫ H.map ((M(k) ⋙ T(k)).map α) := D.unit.naturality α
  have h₄ : f = (M(k) ⋙ T(k)).map α ≫ b₁ := by
    have hf : (G.commShiftIso n).hom.app P =
        (T(k)).map ((C.commShiftIso n).hom.app P) ≫
          ((T(k)).commShiftIso n).hom.app (C.obj P) :=
      Functor.commShiftIso_comp_hom_app C (T(k)) n P
    change (G.commShiftIso n).hom.app P = _
    rw [hf, Functor.commShiftIso_comp_hom_app, Functor.map_comp, Category.assoc]
    change _ = (T(k)).map ((M(k)).map α) ≫ ((M(k) ⋙ T(k)).commShiftIso n).hom.app aP
    rw [Functor.commShiftIso_comp_hom_app]
    rfl
  have h₅ : φ y = D.unit.app aP₀ ≫ H.map f := by
    exact (projectiveEffectiveTorusHomEquiv_postcompose k P₀ f (η.hom.app P₀)).trans
      (congrArg (· ≫ H.map f) (hP P₀))
  calc
    _ = α ≫ D.unit.app (aP⟦n⟧) ≫ H.map b₁ ≫ e.hom :=
      h₁.trans (congrArg (α ≫ ·) h₂)
    _ = D.unit.app aP₀ ≫ H.map f ≫ e.hom := by
      rw [← Category.assoc α, h₃, Category.assoc, h₄, H.map_comp, Category.assoc]
    _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ e.hom) h₅.symm)

end AlgebraicGeometry.MotivicHomotopy
