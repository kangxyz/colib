/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.MarkedCoordinate
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryFrameCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryCoordinates

/-! # Exact whole-boundary coordinates over an arbitrary relative base -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable {S X C Y Z D A B : Scheme.{u}} (q : X ⟶ S)
  [IsSeparated q] [SmoothOfRelativeDimension 1 q] (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (z : Z ⟶ X)
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))

local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "σ" => divisorSheafGlobalSection (Scheme.Hom.ker (compactificationGraph π j))
local notation "iI" => infinityProductMap π j d
local notation "iZ" => markedProductMap π j s
local notation "iA" => fullGraphBoundaryMap π j s d

/-- The entire infinity-plus-marked frame is glued from the native canonical
infinity frame and the transported relative target-graph frame. -/
def fullGraphFrame : (Modules.pullback iA).obj F ≅
    SheafOfModules.unit
      (pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π)).ringCatSheaf :=
  Classical.choose (exists_boundaryCoprod_frame iI iZ F
    (compactificationInfinityDivisorFrame π j d hd)
    (compactificationMarkedFrame q π j p hq z s hs H e))

/-- The actual whole-boundary coordinate of the canonical graph section. -/
def fullGraphCoordinate :
    Γ((pullback (pullback.snd (j ≫ π) π) d ⨿ pullback (j ≫ π) (s ≫ j ≫ π) : Scheme), ⊤) :=
  (fullGraphFrame q π j p hq z s hs H e d hd).hom.app ⊤
    (pullbackGlobalSections iA F σ)

@[simp]
theorem fullGraphCoordinate_infinity :
    (coprod.inl : pullback (pullback.snd (j ≫ π) π) d ⟶ _).appTop
      (fullGraphCoordinate q π j p hq z s hs H e d hd) = 1 := by
  exact (boundaryCoprodFrame_inl_coordinate _ _ _ _ _
    (Classical.choose_spec (exists_boundaryCoprod_frame iI iZ F
      (compactificationInfinityDivisorFrame π j d hd)
      (compactificationMarkedFrame q π j p hq z s hs H e))).1 σ).trans
        (compactificationInfinityDivisorFrame_coordinate π j d hd)

@[simp]
theorem fullGraphCoordinate_mark :
    (coprod.inr : pullback (j ≫ π) (s ≫ j ≫ π) ⟶ _).appTop
      (fullGraphCoordinate q π j p hq z s hs H e d hd) =
        (markedProductToTarget q π j p hq z s hs).appTop (targetCoordinate q z e) := by
  exact (boundaryCoprodFrame_inr_coordinate _ _ _ _ _
    (Classical.choose_spec (exists_boundaryCoprod_frame iI iZ F
      (compactificationInfinityDivisorFrame π j d hd)
      (compactificationMarkedFrame q π j p hq z s hs H e))).2 σ).trans
        (compactificationMarkedFrame_coordinate q π j p hq z s hs H e)

variable (a : A ⟶ X) (ha : Disjoint (Set.range a) (Set.range z))

/-- The scalar on the complete independent correction boundary. -/
def fullCorrectionUnit :
    SheafOfModules.unit
      (pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)).ringCatSheaf ≅
    SheafOfModules.unit
      (pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q)).ringCatSheaf :=
  Classical.choose (exists_boundaryCoprod_unitAutomorphism _ _ (correctionUnit q z e a ha))

/-- Its native global scalar, not a supplied coordinate. -/
def fullCorrectionCoordinate :
    Γ((pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q) : Scheme), ⊤) :=
  Modules.Hom.app
    (X := pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q))
    (fullCorrectionUnit q π z e d a ha).hom ⊤
    (1 : Γ((pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q) : Scheme), ⊤))

omit [IsSeparated π] in
@[simp]
theorem fullCorrectionCoordinate_infinity :
    (coprod.inl : pullback (pullback.snd (a ≫ q) π) d ⟶ _).appTop
      (fullCorrectionCoordinate q π z e d a ha) = 1 := by
  apply unitAutomorphism_coordinate_of_restriction _ _ (Iso.refl _)
  have he : (Modules.restrictFunctor (coprod.inl :
      pullback (pullback.snd (a ≫ q) π) d ⟶ _)).map
        (fullCorrectionUnit q π z e d a ha).hom = 𝟙 _ :=
    (Classical.choose_spec (exists_boundaryCoprod_unitAutomorphism _ _
      (correctionUnit q z e a ha))).1
  rw [he]
  let m := (Modules.restrictUnitIso (coprod.inl :
    pullback (pullback.snd (a ≫ q) π) d ⟶
      pullback (pullback.snd (a ≫ q) π) d ⨿ pullback (a ≫ q) (z ≫ q))).hom
  change 𝟙 _ ≫ m = m ≫ 𝟙 _
  exact (Category.id_comp m).trans (Category.comp_id m).symm

omit [IsSeparated π] in
@[simp]
theorem fullCorrectionCoordinate_mark :
    (coprod.inr : pullback (a ≫ q) (z ≫ q) ⟶ _).appTop
      (fullCorrectionCoordinate q π z e d a ha) = correctionCoordinate q z e a := by
  rw [← correctionUnit_coordinate q z e a ha]
  apply unitAutomorphism_coordinate_of_restriction
  exact (Classical.choose_spec (exists_boundaryCoprod_unitAutomorphism _ _
    (correctionUnit q z e a ha))).2

variable (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)

omit [IsSeparated q] [SmoothOfRelativeDimension 1 q] [IsSeparated π]
  [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)] in
/-- Both whole marked-product maps go to the same actual target marked product. -/
theorem commonMarkedProductToTarget_eq :
    commonZeroToLambda π j α s ≫ markedProductToTarget q π j p hq z s hs =
      commonZeroToPsi q π j p hq a α β h z s hs ≫ correctionProductToTarget q z a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, markedProductToTarget_fst, correctionProductToTarget,
      retainedSourceChange_fst, commonZeroToLambda, retainedSourceChange_fst_assoc,
      commonZeroToPsi, pullback.lift_fst_assoc]
    simpa only [Category.assoc] using
      congrArg (fun f => pullback.fst (commonProjection π j α) (s ≫ j ≫ π) ≫ f) h
  · simp [commonZeroToLambda, commonZeroToPsi, markedProductToTarget,
      correctionProductToTarget, Category.assoc]

private theorem regularFunction_comp_apply {P Q R : Scheme.{u}}
    (f : P ⟶ Q) (g : Q ⟶ R) (x : Γ(R, ⊤)) :
    f.appTop (g.appTop x) = (f ≫ g).appTop x := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

private theorem regularFunction_restrict_coprod_inl {P Q R T : Scheme.{u}}
    (f : P ⟶ R) (g : Q ⟶ T) (x : Γ(R ⨿ T, ⊤)) :
    (coprod.inl : P ⟶ P ⨿ Q).appTop ((coprod.map f g).appTop x) =
      f.appTop ((coprod.inl : R ⟶ R ⨿ T).appTop x) := by
  rw [regularFunction_comp_apply, coprod.inl_map, ← regularFunction_comp_apply]

private theorem regularFunction_restrict_coprod_inr {P Q R T : Scheme.{u}}
    (f : P ⟶ R) (g : Q ⟶ T) (x : Γ(R ⨿ T, ⊤)) :
    (coprod.inr : Q ⟶ P ⨿ Q).appTop ((coprod.map f g).appTop x) =
      g.appTop ((coprod.inr : T ⟶ R ⨿ T).appTop x) := by
  rw [regularFunction_comp_apply, coprod.inr_map, ← regularFunction_comp_apply]

/-- The graph coordinate and independent correction unit agree on the complete
common boundary, from the actual original source square. -/
theorem commonBoundaryCoordinate_eq :
    (commonBoundaryToLambda π j α s d).appTop
      (fullGraphCoordinate q π j p hq z s hs H e d hd) =
    (commonBoundaryToPsi q π j p hq a α β h z s hs d).appTop
      (fullCorrectionCoordinate q π z e d a ha) := by
  let f := constantInfinitySourceMap α (j ≫ π) π (commonProjection π j α) rfl d
  let f' := constantInfinitySourceMap β (a ≫ q) π (commonProjection π j α)
    (commonProjection_fixed q π j p hq a α β h) d
  let g := commonZeroToLambda π j α s
  let g' := commonZeroToPsi q π j p hq a α β h z s hs
  let x := fullGraphCoordinate q π j p hq z s hs H e d hd
  let y := fullCorrectionCoordinate q π z e d a ha
  change (coprod.map f g).appTop x = (coprod.map f' g').appTop y
  apply globalSections_coprod_ext
  · rw [regularFunction_restrict_coprod_inl f g x, regularFunction_restrict_coprod_inl f' g' y]
    have hx : (coprod.inl : pullback (pullback.snd (j ≫ π) π) d ⟶ _).appTop x = 1 :=
      fullGraphCoordinate_infinity q π j p hq z s hs H e d hd
    have hy : (coprod.inl : pullback (pullback.snd (a ≫ q) π) d ⟶ _).appTop y = 1 :=
      fullCorrectionCoordinate_infinity q π z e d a ha
    simp only [hx, hy, map_one]
  · rw [regularFunction_restrict_coprod_inr f g x, regularFunction_restrict_coprod_inr f' g' y]
    let m := markedProductToTarget q π j p hq z s hs
    let m' := correctionProductToTarget q z a
    let b := targetCoordinate q z e
    have hx : (coprod.inr : pullback (j ≫ π) (s ≫ j ≫ π) ⟶ _).appTop x =
        m.appTop b := fullGraphCoordinate_mark q π j p hq z s hs H e d hd
    have hy : (coprod.inr : pullback (a ≫ q) (z ≫ q) ⟶ _).appTop y =
        m'.appTop b := fullCorrectionCoordinate_mark q π z e d a ha
    rw [hx, hy, regularFunction_comp_apply g m b, regularFunction_comp_apply g' m' b]
    exact congrArg (fun f => f.appTop b)
      (commonMarkedProductToTarget_eq q π j p hq z s hs a α β h)

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
