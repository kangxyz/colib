/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedForgetShift
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveExact
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.AdjunctionShift
import StacksFrontier.Algebra.Homology.HomotopyCategory.MapCompIsoCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionCommShift

/-! # Native shift comparisons for the projective and injective torus models -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "NST" => LargeSheaves k
local notation "PST" => LargePresheaves k
local notation "c" => ComplexShape.up ℤ
local notation "S" => nisnevichSheafify k
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "U" => SheafWithTransfers.forget k
local notation "T" => (withParameterFunctor Gₘ : PST ⥤ PST)
local notation "R" => forgetDerivedFunctor k
local notation "Qₚ" => DerivedCategory.Qh (C := PST)
local notation "Qₛ" => DerivedCategory.Qh (C := NST)
local notation "V" => DerivedCategory.Minus.ι (C := NST)

/-- The abelian structure on transfer sheaves for the shifted injective torus representatives. -/
local instance instAbelianTorusRepresentativeShift : Abelian NST := SheafWithTransfers.abelian k

instance torusInjectiveModelsStableUnderShift :
    ObjectProperty.IsStableUnderShift
      (fun I : HomotopyCategory NST c => CochainComplex.IsKInjective I.as) ℤ where
  isStableUnderShiftBy n := ⟨fun I hI => by
    let Q := HomotopyCategory.quotient NST c
    change CochainComplex.IsKInjective (((Q.obj I.as)⟦n⟧).as)
    rw [HomotopyCategory.shift_quotient_obj]
    exact (CochainComplex.isKInjective_shift_iff I.as n).2 hI⟩

/-- The homotopy-level torus transpose uses the termwise commutation with shift. -/
instance torusTensorHomotopyAdjunctionCommShift : (torusTensorHomotopyAdjunction k).CommShift ℤ :=
  Adjunction.mapHomotopyCategoryAdjunction_commShift
    ((parameterTensorAdjunction Gₘ).comp (nisnevichSheafificationAdjunction k))

private theorem composeShiftSquares {C : Type*} [Category* C] {L : C ⥤ C}
    {A B D : C} {A' B' D' : C}
    {a : A' ⟶ L.obj A} {b : B' ⟶ L.obj B} {d : D' ⟶ L.obj D}
    {f : A ⟶ B} {g : B ⟶ D} {f' : A' ⟶ B'} {g' : B' ⟶ D'}
    (hf : a ≫ L.map f = f' ≫ b) (hg : b ≫ L.map g = g' ≫ d) :
    a ≫ L.map (f ≫ g) = (f' ≫ g') ≫ d := by
  rw [L.map_comp, ← Category.assoc a, hf, Category.assoc, hg, Category.assoc]

set_option maxHeartbeats 650000 in
-- The four actual functors and the three termwise comparisons retain their native shifts.
/-- The comparison used to reindex injective representatives preserves the native shift. -/
theorem torusTensorInjectiveReindexingIso_commShift :
    NatTrans.CommShift (torusTensorInjectiveReindexingIso k).hom ℤ := by
  let J := torusTensorInjectiveInclusion k
  let Q := Qₚ
  let H := (U ⋙ T).mapHomotopyCategory c
  let F := (U).mapHomotopyCategory c
  let G := (T).mapHomotopyCategory c
  let E := (T).mapDerivedCategory
  let X := J ⋙ H ⋙ Q
  let Y := J ⋙ (F ⋙ G) ⋙ Q
  let Z := (J ⋙ F) ⋙ Q ⋙ E
  let W := (J ⋙ (Qₛ) ⋙ R) ⋙ E
  let W' := torusTensorInjectiveToDerived k ⋙ torusTensorDerivedRight k
  let f := Functor.mapHomotopyCategoryCompIso (Iso.refl (U ⋙ T)) c
  let g := (T).mapDerivedCategoryFactorsh
  let τ := forgetHomotopyUnit k
  let η := torusTensorInjectiveReindexingIso k
  let j₁ : X ⟶ Y := Functor.whiskerLeft J (Functor.whiskerRight f.inv Q)
  let j₂ : Y ⟶ Z :=
    Functor.whiskerLeft J (Functor.associator F G Q).hom ≫
    (Functor.associator J F (G ⋙ Q)).inv ≫
    Functor.whiskerLeft (J ⋙ F) g.inv
  let Z' := (J ⋙ F ⋙ Q) ⋙ E
  let j₃ : Z' ⟶ W := Functor.whiskerRight (Functor.whiskerLeft J τ) E
  have h (I : TorusTensorInjectiveHomotopy k) :
      η.hom.app I = j₁.app I ≫ j₂.app I ≫ j₃.app I := by
    simp only [η, j₁, j₂, j₃, torusTensorInjectiveReindexingIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Category.assoc,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    exact congrArg (Q.map (f.inv.app (J.obj I)) ≫ ·) (Category.id_comp _).symm
  let : NatTrans.CommShift f.hom ℤ := inferInstance
  let : NatTrans.CommShift f.inv ℤ := NatTrans.CommShift.of_iso_inv f ℤ
  let : NatTrans.CommShift g.hom ℤ := inferInstance
  let : NatTrans.CommShift g.inv ℤ := NatTrans.CommShift.of_iso_inv g ℤ
  let : NatTrans.CommShift j₁ ℤ := by dsimp only [j₁]; infer_instance
  let : NatTrans.CommShift τ ℤ := forgetHomotopyUnitCommShift k
  let τJ := Functor.whiskerLeft J τ
  let : NatTrans.CommShift τJ ℤ := by dsimp only [τJ]; infer_instance
  let : NatTrans.CommShift j₃ ℤ := NatTrans.CommShift.whiskerRight τJ E ℤ
  refine ⟨fun n => NatTrans.ext (funext fun I => ?_)⟩
  have hX := NatTrans.shift_app_comm j₁ n I
  have hZ := NatTrans.shift_app_comm j₃ n I
  let j₂₀ := Functor.whiskerLeft (J ⋙ F) g.inv
  let : NatTrans.CommShift j₂₀ ℤ := by dsimp only [j₂₀]; infer_instance
  have hY := NatTrans.shift_app_comm j₂₀ n I
  have he (I : TorusTensorInjectiveHomotopy k) :
      j₂.app I = g.inv.app ((J ⋙ F).obj I) := by
    simp only [j₂, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Category.id_comp]
    exact Category.id_comp _
  have hY₀ : (Y.commShiftIso n).hom.app I ≫ (j₂.app I)⟦n⟧' =
      j₂.app (I⟦n⟧) ≫ (Z.commShiftIso n).hom.app I := by
    rw [he, he]
    have hYY : (Y.commShiftIso n).hom.app I =
        (((J ⋙ F) ⋙ G ⋙ Q).commShiftIso n).hom.app I := by
      simp only [Y, Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.map_comp,
        Category.assoc, Functor.comp_obj]
    rw [hYY]
    exact hY
  have hZZ : (Z.commShiftIso n).hom.app I = (Z'.commShiftIso n).hom.app I := by
    simp only [Z, Z', Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.map_comp,
      Category.assoc, Functor.comp_obj]
  have hW : (W.commShiftIso n).hom.app I = (W'.commShiftIso n).hom.app I := by
    simp only [W, W', torusTensorInjectiveToDerived, torusTensorDerivedRight,
      Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.map_comp, Category.assoc,
      Functor.comp_obj]
    rfl
  change (X.commShiftIso n).hom.app I ≫ (η.hom.app I)⟦n⟧' =
    η.hom.app (I⟦n⟧) ≫ (W'.commShiftIso n).hom.app I
  rw [h, h, ← hW]
  have hZY : (Z.commShiftIso n).hom.app I ≫ (j₃.app I)⟦n⟧' =
      j₃.app (I⟦n⟧) ≫ (W.commShiftIso n).hom.app I := by
    rw [hZZ]
    exact hZ
  exact composeShiftSquares hX (composeShiftSquares hY₀ hZY)

set_option maxHeartbeats 550000 in
-- The representative formula compares exactly two quotient maps and the reindexing iso.
/-- On the actual projective and K-injective models, shifting a torus transpose shifts
its literal homotopy class through the derived quotient. -/
theorem torusTensorHomEquivOnRepresentatives_shift_map
    (P : BoundedAboveProjectiveHomotopy k) (I : TorusTensorInjectiveHomotopy k)
    (f : (((parameterTensorFunctor Gₘ ⋙ S).mapHomotopyCategory c).obj P.obj) ⟶ I.obj)
    (n : ℤ) :
    let H := (parameterTensorFunctor Gₘ ⋙ S).mapHomotopyCategory c
    let J := torusTensorInjectiveToDerived k
    let D := torusTensorDerivedRight k
    let p := ((projInclusion k).commShiftIso n).hom.app P
    let i := ((torusTensorInjectiveInclusion k).commShiftIso n).inv.app I
    let α := (H.commShiftIso n).hom.app P.obj
    let f' := H.map p ≫ α ≫ f⟦n⟧' ≫ i
    torusTensorHomEquivOnRepresentatives k (P⟦n⟧) (I⟦n⟧) ((Qₛ).map f') ≫
      ((J ⋙ D).commShiftIso n).hom.app I =
      ((projInclusion k ⋙ Qₚ).commShiftIso n).hom.app P ≫
        (torusTensorHomEquivOnRepresentatives k P I ((Qₛ).map f))⟦n⟧' := by
  intro H J D p i α f'
  let B := (U ⋙ T).mapHomotopyCategory c
  let adj := torusTensorHomotopyAdjunction k
  let η := torusTensorInjectiveReindexingIso k
  let := torusTensorInjectiveReindexingIso_commShift k
  let t := adj.homEquiv P.obj I.obj f
  let t' := adj.homEquiv (P⟦n⟧).obj (I⟦n⟧).obj f'
  let t₀ := adj.homEquiv (P.obj⟦n⟧) (I.obj⟦n⟧) (α ≫ f⟦n⟧')
  have h := adj.homEquiv_shift_transport f n
  change t₀ ≫ (B.commShiftIso n).hom.app I.obj = t⟦n⟧' at h
  have ht : t' = p ≫ t₀ ≫ B.map i := by
    dsimp only [t', f', t₀]
    rw [adj.homEquiv_naturality_left]
    rw [← Category.assoc α, adj.homEquiv_naturality_right]
    rfl
  rw [tensorHomOnRepresentatives_map, tensorHomOnRepresentatives_map]
  change ((Qₚ).map t' ≫ η.hom.app (I⟦n⟧)) ≫ ((J ⋙ D).commShiftIso n).hom.app I =
    ((projInclusion k ⋙ Qₚ).commShiftIso n).hom.app P ≫
      ((Qₚ).map t ≫ η.hom.app I)⟦n⟧'
  rw [Category.assoc, ← NatTrans.shift_app_comm η.hom n I, Functor.map_comp]
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc]
  let j := ((torusTensorInjectiveInclusion k).commShiftIso n).hom.app I
  let β := (B.commShiftIso n).hom.app I.obj
  let γ := ((Qₚ).commShiftIso n).hom.app (B.obj I.obj)
  let z := (η.hom.app I)⟦n⟧'
  change (Qₚ).map t' ≫ (Qₚ).map (B.map j) ≫ (Qₚ).map β ≫ γ ≫ z =
    (Qₚ).map p ≫ ((Qₚ).commShiftIso n).hom.app P.obj ≫ ((Qₚ).map t)⟦n⟧' ≫ z
  have hi : i ≫ j = 𝟙 _ := Iso.inv_hom_id_app _ _
  have hv : t' ≫ B.map j ≫ β = p ≫ t⟦n⟧' := by
    rw [ht]
    simp only [Category.assoc]
    have hh : B.map i ≫ B.map j = 𝟙 _ :=
      ((B.map_comp i j).symm.trans ((B.congr_map hi).trans (B.map_id _)))
    rw [← Category.assoc (B.map i), hh, Category.id_comp, h]
  calc
    _ = (Qₚ).map (t' ≫ B.map j ≫ β) ≫ γ ≫ z := by
      simp only [(Qₚ).map_comp, Category.assoc]
    _ = (Qₚ).map p ≫ (Qₚ).map (t⟦n⟧') ≫ γ ≫ z := by
      rw [hv, (Qₚ).map_comp, Category.assoc]
    _ = _ := by
      have hh := ((Qₚ).commShiftIso n).hom.naturality_assoc t z
      exact congrArg ((Qₚ).map p ≫ ·) hh

/-- The unreduced projective model uses the shift of the original termwise tensor
and the bounded-above derived Nisnevich functor. -/
instance projectiveTorusTensorToDerivedMinusCommShift :
    (projectiveTorusTensorToDerivedMinus k).CommShift ℤ := by
  unfold projectiveTorusTensorToDerivedMinus
  infer_instance

/-- The projective torus model shifts by the composite of its two functor shifts. -/
theorem projectiveTorusTensorToDerivedMinus_commShiftIso_hom_app
    (n : ℤ) (K : DerivedCategory.Minus PST) :
    ((projectiveTorusTensorToDerivedMinus k).commShiftIso n).hom.app K =
      (((projectiveDerivedMinusFunctor k (parameterTensorFunctor Gₘ)) ⋙
        (S).mapDerivedCategoryMinus).commShiftIso n).hom.app K :=
  (rfl)

end AlgebraicGeometry.SheafWithTransfers
