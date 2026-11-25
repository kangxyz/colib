/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenCarrier
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNervePointwiseFamily
public import Colib.Topology.Prespectrum.MappingCone

/-!
# Evaluation on the two actual reference attachments

Both displayed pushouts descend their original levelwise formulas into the reduced
mapping-cone prespectrum. The evaluation on the Laurent summand is the actual cone
inclusion; both cylinder coordinates remain unchanged; both distinct tips evaluate
to the same native point. The restrictions to compact parameters in one specified
summand are jointly continuous. The five actual summands show that the whole
evaluator respects the native point and structure maps. No global continuity
is asserted for a product with the carrier.

Adapted from `CommonReferenceNerveCutOpenEvaluation.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopCat
open Topology
open scoped Simplicial Topology unitInterval
universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
open SmallWaldhausenCategory

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ T)
  (G : V ⟶ T) (ε₀ ε₁ : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)

/-- The original levelwise reduced mapping-cone prespectrum of the specified model map. -/
abbrev nativeCone : LoopPrespectrum.{u} := LoopPrespectrum.mappingCone (prespectrumMap J)

/-- The literal cylinder formula, with the actual carrier interval in universe `u`. -/
def nativeCylinderValue (n : ℕ) (z : |parameterSSet F| × TopCat.I.{u})
    (x : (prespectrum V).space n) : (nativeCone J).space n :=
  ReducedMappingCone.cylinder ((prespectrum W).point n) ((prespectrum T).point n)
    ((prespectrumMap J).map n) (z.2.down, pointwisePrespectrumFamily F n z.1 x)

/-- The original Laurent family followed by its native mapping-cone inclusion. -/
def nativeLaurentValue (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum V).space n) : (nativeCone J).space n :=
  (LoopPrespectrum.mappingConeInclusion (prespectrumMap J)).map n
    (pointwisePrespectrumFamily G n y x)

/-- The first endpoint-pair values used in the exposed set-level descent. -/
def firstEndsValue (n : ℕ) (z : |parameterSSet G| ⊕ |tipSSet.{u}|)
    (x : (prespectrum V).space n) : (nativeCone J).space n :=
  Sum.elim (nativeLaurentValue J G n) (fun _ _ ↦ (nativeCone J).point n) z x

/-- The complete first endpoint square for the actual exposed descent data. -/
theorem first_value_square (n : ℕ) :
    (forget TopCat).map (TopCat.intervalEndpoints |parameterSSet F|) ≫
        (↾(nativeCylinderValue F J n)) =
      (forget TopCat).map (DoubleCylinder.endMap
        (SSet.toTop.map (attaching F J G ε₀)) (SSet.toTop.map (erase F))) ≫
        (↾(firstEndsValue J G n)) := by
  apply ConcreteCategory.hom_ext
  intro z
  funext x
  rcases z with y | y
  · change ReducedMappingCone.cylinder _ _ _ (0, pointwisePrespectrumFamily F n y x) =
      ReducedMappingCone.inr _ _ _
        (pointwisePrespectrumFamily G n (mapParameter (attachPostcompNode F J G ε₀) y) x)
    rw [ReducedMappingCone.cylinder_zero]
    exact congrArg (ReducedMappingCone.inr ((prespectrum W).point n)
      ((prespectrum T).point n) ((prespectrumMap J).map n))
      (pointwisePrespectrumFamily_attachPostcomp F J G ε₀ n y x).symm
  · exact ReducedMappingCone.cylinder_one _ _ _ _

/-- Descend the literal first cylinder and Laurent/tip values through its actual set pushout. -/
def firstNativeEval (n : ℕ) :
    |firstSimplicial F J G ε₀| → (prespectrum V).space n → (nativeCone J).space n :=
  ((first_isPushout F J G ε₀).map (forget TopCat)).desc
    (↾(nativeCylinderValue F J n)) (↾(firstEndsValue J G n))
    (first_value_square F J G ε₀ n)

private theorem firstNativeEval_cylinder (n : ℕ)
    (z : |parameterSSet F| × TopCat.I.{u}) (x : (prespectrum V).space n) :
    firstNativeEval F J G ε₀ n
        (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F) z) x =
      nativeCylinderValue F J n z x :=
  congrFun (ConcreteCategory.congr_hom
    (((first_isPushout F J G ε₀).map (forget TopCat)).inl_desc
      (↾(nativeCylinderValue F J n)) (↾(firstEndsValue J G n))
      (first_value_square F J G ε₀ n)) z) x

private theorem firstNativeEval_ends (n : ℕ)
    (z : |parameterSSet G| ⊕ |tipSSet.{u}|) (x : (prespectrum V).space n) :
    firstNativeEval F J G ε₀ n
        (DoubleCylinder.realizedEnds (attaching F J G ε₀) (erase F) z) x =
      firstEndsValue J G n z x :=
  congrFun (ConcreteCategory.congr_hom
    (((first_isPushout F J G ε₀).map (forget TopCat)).inr_desc
      (↾(nativeCylinderValue F J n)) (↾(firstEndsValue J G n))
      (first_value_square F J G ε₀ n)) z) x

private theorem eval_realized_left {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (y : |Y|) :
    SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) y =
        DoubleCylinder.realizedEnds f g (Sum.inl y) := by
  have h : SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inl ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
        (realizationBinarySumIso_inl Y Z)
  exact ConcreteCategory.congr_hom h y

private theorem eval_realized_right {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (z : |Z|) :
    SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) z =
        DoubleCylinder.realizedEnds f g (Sum.inr z) := by
  have h : SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inr ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
        (realizationBinarySumIso_inr Y Z)
  exact ConcreteCategory.congr_hom h z

private theorem firstNativeEval_left (n : ℕ)
    (y : |parameterSSet G|) (x : (prespectrum V).space n) :
    firstNativeEval F J G ε₀ n (SSet.toTop.map (left₀ F J G ε₀) y) x =
      nativeLaurentValue J G n y x := by
  exact (congrArg (fun z ↦ firstNativeEval F J G ε₀ n z x)
    (eval_realized_left (attaching F J G ε₀) (erase F) y)).trans
      (firstNativeEval_ends F J G ε₀ n (Sum.inl y) x)

/-- The first descended evaluator and the new tip form the second endpoint-pair values. -/
def secondEndsValue (n : ℕ)
    (z : |firstSimplicial F J G ε₀| ⊕ |tipSSet.{u}|)
    (x : (prespectrum V).space n) : (nativeCone J).space n :=
  Sum.elim (firstNativeEval F J G ε₀ n) (fun _ _ ↦ (nativeCone J).point n) z x

/-- The complete second endpoint square for the actual exposed descent data. -/
theorem second_value_square (n : ℕ) :
    (forget TopCat).map (TopCat.intervalEndpoints |parameterSSet F|) ≫
        (↾(nativeCylinderValue F J n)) =
      (forget TopCat).map (DoubleCylinder.endMap
        (SSet.toTop.map (secondAttaching F J G ε₀ ε₁)) (SSet.toTop.map (erase F))) ≫
        (↾(secondEndsValue F J G ε₀ n)) := by
  apply ConcreteCategory.hom_ext
  intro z
  funext x
  rcases z with y | y
  · change nativeCylinderValue F J n (y, (ULift.up (0 : I) : TopCat.I.{u})) x =
      firstNativeEval F J G ε₀ n (SSet.toTop.map (secondAttaching F J G ε₀ ε₁) y) x
    unfold secondAttaching
    rw [Functor.map_comp]
    change nativeCylinderValue F J n (y, (ULift.up (0 : I) : TopCat.I.{u})) x =
      firstNativeEval F J G ε₀ n
        (SSet.toTop.map (left₀ F J G ε₀) (SSet.toTop.map (attaching F J G ε₁) y)) x
    rw [firstNativeEval_left]
    change ReducedMappingCone.cylinder _ _ _ (0, pointwisePrespectrumFamily F n y x) =
      ReducedMappingCone.inr _ _ _
        (pointwisePrespectrumFamily G n (mapParameter (attachPostcompNode F J G ε₁) y) x)
    rw [ReducedMappingCone.cylinder_zero]
    exact congrArg (ReducedMappingCone.inr ((prespectrum W).point n)
      ((prespectrum T).point n) ((prespectrumMap J).map n))
      (pointwisePrespectrumFamily_attachPostcomp F J G ε₁ n y x).symm
  · exact ReducedMappingCone.cylinder_one _ _ _ _

/-- The actual two-tip realization evaluates in the original native cone at every level. -/
def nativeEval (n : ℕ) :
    space F J G ε₀ ε₁ → (prespectrum V).space n → (nativeCone J).space n :=
  ((second_isPushout F J G ε₀ ε₁).map (forget TopCat)).desc
    (↾(nativeCylinderValue F J n)) (↾(secondEndsValue F J G ε₀ n))
    (second_value_square F J G ε₀ ε₁ n)

private theorem nativeEval_secondCylinder (n : ℕ)
    (z : |parameterSSet F| × TopCat.I.{u}) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n
        (DoubleCylinder.realizedCylinder (secondAttaching F J G ε₀ ε₁) (erase F) z) x =
      nativeCylinderValue F J n z x :=
  congrFun (ConcreteCategory.congr_hom
    (((second_isPushout F J G ε₀ ε₁).map (forget TopCat)).inl_desc
      (↾(nativeCylinderValue F J n)) (↾(secondEndsValue F J G ε₀ n))
      (second_value_square F J G ε₀ ε₁ n)) z) x

private theorem nativeEval_secondEnds (n : ℕ)
    (z : |firstSimplicial F J G ε₀| ⊕ |tipSSet.{u}|) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n
        (DoubleCylinder.realizedEnds (secondAttaching F J G ε₀ ε₁) (erase F) z) x =
      secondEndsValue F J G ε₀ n z x :=
  congrFun (ConcreteCategory.congr_hom
    (((second_isPushout F J G ε₀ ε₁).map (forget TopCat)).inr_desc
      (↾(nativeCylinderValue F J n)) (↾(secondEndsValue F J G ε₀ n))
      (second_value_square F J G ε₀ ε₁ n)) z) x

private theorem nativeEval_first (n : ℕ)
    (y : |firstSimplicial F J G ε₀|) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n (SSet.toTop.map (left₁ F J G ε₀ ε₁) y) x =
      firstNativeEval F J G ε₀ n y x := by
  exact (congrArg (fun z ↦ nativeEval F J G ε₀ ε₁ n z x)
    (eval_realized_left (secondAttaching F J G ε₀ ε₁) (erase F) y)).trans
      (nativeEval_secondEnds F J G ε₀ ε₁ n (Sum.inl y) x)

/-- The unchanged Laurent summand evaluates by the original mapping-cone inclusion. -/
theorem nativeEval_laurentInclusion (n : ℕ)
    (y : |parameterSSet G|) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n (laurentInclusion F J G ε₀ ε₁ y) x =
      (LoopPrespectrum.mappingConeInclusion (prespectrumMap J)).map n
        (pointwisePrespectrumFamily G n y x) := by
  change nativeEval F J G ε₀ ε₁ n
    (SSet.toTop.map (left₁ F J G ε₀ ε₁) (SSet.toTop.map (left₀ F J G ε₀) y)) x = _
  rw [nativeEval_first, firstNativeEval_left]
  rfl

/-- The first cylinder retains its actual coordinate and native input, including level zero. -/
theorem nativeEval_cylinderMinus (n : ℕ)
    (y : |parameterSSet F|) (c : I) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n (cylinderMinus F J G ε₀ ε₁ (y, c)) x =
      ReducedMappingCone.cylinder ((prespectrum W).point n) ((prespectrum T).point n)
        ((prespectrumMap J).map n) (c, pointwisePrespectrumFamily F n y x) := by
  change nativeEval F J G ε₀ ε₁ n (SSet.toTop.map (left₁ F J G ε₀ ε₁)
    (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F)
      (y, (ULift.up c : TopCat.I.{u})))) x = _
  rw [nativeEval_first, firstNativeEval_cylinder]
  rfl

/-- The second cylinder uses the same native formula with its separately retained tip. -/
theorem nativeEval_cylinderPlus (n : ℕ)
    (y : |parameterSSet F|) (c : I) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n (cylinderPlus F J G ε₀ ε₁ (y, c)) x =
      ReducedMappingCone.cylinder ((prespectrum W).point n) ((prespectrum T).point n)
        ((prespectrumMap J).map n) (c, pointwisePrespectrumFamily F n y x) :=
  nativeEval_secondCylinder F J G ε₀ ε₁ n (y, (ULift.up c : TopCat.I.{u})) x

/-- The first tip evaluates to the native point, without identifying the two carrier tips. -/
theorem nativeEval_tipMinus (n : ℕ) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n (tipMinus F J G ε₀ ε₁) x = (nativeCone J).point n := by
  exact (nativeEval_first F J G ε₀ ε₁ n
    (SSet.toTop.map (right₀ F J G ε₀) (default : |tipSSet.{u}|)) x).trans
      ((congrArg (fun z ↦ firstNativeEval F J G ε₀ n z x)
        (eval_realized_right (attaching F J G ε₀) (erase F)
          (default : |tipSSet.{u}|))).trans
        (firstNativeEval_ends F J G ε₀ n (Sum.inr (default : |tipSSet.{u}|)) x))

/-- The new tip also evaluates to the same native point. -/
theorem nativeEval_tipPlus (n : ℕ) (x : (prespectrum V).space n) :
    nativeEval F J G ε₀ ε₁ n (tipPlus F J G ε₀ ε₁) x = (nativeCone J).point n := by
  exact (congrArg (fun z ↦ nativeEval F J G ε₀ ε₁ n z x)
    (eval_realized_right (secondAttaching F J G ε₀ ε₁) (erase F)
      (default : |tipSSet.{u}|))).trans
        (nativeEval_secondEnds F J G ε₀ ε₁ n (Sum.inr (default : |tipSSet.{u}|)) x)

/-- A compact parameter in the Laurent summand has the original joint continuity. -/
theorem nativeEval_laurent_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |parameterSSet G|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n (laurentInclusion F J G ε₀ ε₁ (p z.1)) z.2) := by
  have h : (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n (laurentInclusion F J G ε₀ ε₁ (p z.1)) z.2) =
      (fun z ↦ (LoopPrespectrum.mappingConeInclusion (prespectrumMap J)).map n
        (compactPrespectrumFamily G p n z)) := by
    funext z
    rw [nativeEval_laurentInclusion, pointwisePrespectrumFamily_eq_compact]
  rw [h]
  exact ((LoopPrespectrum.mappingConeInclusion (prespectrumMap J)).map n).continuous.comp
    (compactPrespectrumFamily G p n).continuous

/-- The first whole compact cylinder family is jointly continuous with arbitrary native input. -/
theorem nativeEval_cylinderMinus_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |parameterSSet F|)) (c : C(S, I)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n (cylinderMinus F J G ε₀ ε₁ (p z.1, c z.1)) z.2) := by
  have h : (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n (cylinderMinus F J G ε₀ ε₁ (p z.1, c z.1)) z.2) =
      (fun z ↦ ReducedMappingCone.cylinder ((prespectrum W).point n)
        ((prespectrum T).point n) ((prespectrumMap J).map n)
        (c z.1, compactPrespectrumFamily F p n z)) := by
    funext z
    rw [nativeEval_cylinderMinus, pointwisePrespectrumFamily_eq_compact]
  rw [h]
  fun_prop

/-- The second whole compact cylinder family has the same actual continuity formula. -/
theorem nativeEval_cylinderPlus_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, |parameterSSet F|)) (c : C(S, I)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n (cylinderPlus F J G ε₀ ε₁ (p z.1, c z.1)) z.2) := by
  have h : (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n (cylinderPlus F J G ε₀ ε₁ (p z.1, c z.1)) z.2) =
      (fun z ↦ ReducedMappingCone.cylinder ((prespectrum W).point n)
        ((prespectrum T).point n) ((prespectrumMap J).map n)
        (c z.1, compactPrespectrumFamily F p n z)) := by
    funext z
    rw [nativeEval_cylinderPlus, pointwisePrespectrumFamily_eq_compact]
  rw [h]
  fun_prop

/-- Every actual carrier point lies in one of its original five set-level summands. -/
theorem exists_native_cell (y : space F J G ε₀ ε₁) :
    (∃ z, laurentInclusion F J G ε₀ ε₁ z = y) ∨
      (∃ z c, cylinderMinus F J G ε₀ ε₁ (z, c) = y) ∨
      (∃ z c, cylinderPlus F J G ε₀ ε₁ (z, c) = y) ∨
      tipMinus F J G ε₀ ε₁ = y ∨ tipPlus F J G ε₀ ε₁ = y := by
  rcases Types.eq_or_eq_of_isPushout
      ((second_isPushout F J G ε₀ ε₁).map (forget TopCat)) y with
    ⟨⟨z, c⟩, hz⟩ | ⟨z | z, hz⟩
  · exact Or.inr (Or.inr (Or.inl ⟨z, c.down, hz⟩))
  · have hz' : SSet.toTop.map (left₁ F J G ε₀ ε₁) z = y :=
      (eval_realized_left (secondAttaching F J G ε₀ ε₁) (erase F) z).trans hz
    rcases Types.eq_or_eq_of_isPushout
        ((first_isPushout F J G ε₀).map (forget TopCat)) z with
      ⟨⟨w, c⟩, hw⟩ | ⟨w | w, hw⟩
    · refine Or.inr (Or.inl ⟨w, c.down, ?_⟩)
      exact (congrArg (SSet.toTop.map (left₁ F J G ε₀ ε₁)) hw).trans hz'
    · refine Or.inl ⟨w, ?_⟩
      exact (congrArg (SSet.toTop.map (left₁ F J G ε₀ ε₁))
        ((eval_realized_left (attaching F J G ε₀) (erase F) w).trans hw)).trans hz'
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      have ht : (default : |tipSSet.{u}|) = w := Subsingleton.elim _ _
      have hw' : SSet.toTop.map (right₀ F J G ε₀) (default : |tipSSet.{u}|) = z :=
        (congrArg (SSet.toTop.map (right₀ F J G ε₀)) ht).trans
          ((eval_realized_right (attaching F J G ε₀) (erase F) w).trans hw)
      exact (congrArg (SSet.toTop.map (left₁ F J G ε₀ ε₁)) hw').trans hz'
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    have ht : (default : |tipSSet.{u}|) = z := Subsingleton.elim _ _
    exact (congrArg (SSet.toTop.map (right₁ F J G ε₀ ε₁)) ht).trans
      ((eval_realized_right (secondAttaching F J G ε₀ ε₁) (erase F) z).trans hz)

/-- All carrier values preserve the original native point, in every level. -/
theorem nativeEval_point (n : ℕ) (y : space F J G ε₀ ε₁) :
    nativeEval F J G ε₀ ε₁ n y ((prespectrum V).point n) = (nativeCone J).point n := by
  rcases exists_native_cell F J G ε₀ ε₁ y with
    ⟨z, rfl⟩ | ⟨z, c, rfl⟩ | ⟨z, c, rfl⟩ | rfl | rfl
  · rw [nativeEval_laurentInclusion, pointwisePrespectrumFamily_point]
    rfl
  · rw [nativeEval_cylinderMinus, pointwisePrespectrumFamily_point]
    exact ReducedMappingCone.cylinder_base _ _ _ c
  · rw [nativeEval_cylinderPlus, pointwisePrespectrumFamily_point]
    exact ReducedMappingCone.cylinder_base _ _ _ c
  · exact nativeEval_tipMinus F J G ε₀ ε₁ n _
  · exact nativeEval_tipPlus F J G ε₀ ε₁ n _

/-- The whole evaluator respects the original structure map at an independent time. -/
theorem nativeEval_structure (n : ℕ) (y : space F J G ε₀ ε₁)
    (x : (prespectrum V).space n) (t : I) :
    nativeEval F J G ε₀ ε₁ (n + 1) y ((prespectrum V).structureMap n x t) =
      (nativeCone J).structureMap n (nativeEval F J G ε₀ ε₁ n y x) t := by
  rcases exists_native_cell F J G ε₀ ε₁ y with
    ⟨z, rfl⟩ | ⟨z, c, rfl⟩ | ⟨z, c, rfl⟩ | rfl | rfl
  · rw [nativeEval_laurentInclusion, nativeEval_laurentInclusion,
      pointwisePrespectrumFamily_structure]
    rfl
  · rw [nativeEval_cylinderMinus, nativeEval_cylinderMinus,
      pointwisePrespectrumFamily_structure]
    rfl
  · rw [nativeEval_cylinderPlus, nativeEval_cylinderPlus,
      pointwisePrespectrumFamily_structure]
    rfl
  · rw [nativeEval_tipMinus, nativeEval_tipMinus, (nativeCone J).map_point]
    rfl
  · rw [nativeEval_tipPlus, nativeEval_tipPlus, (nativeCone J).map_point]
    rfl

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
