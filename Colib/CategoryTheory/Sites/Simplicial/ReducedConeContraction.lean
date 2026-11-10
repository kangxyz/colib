/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.SimplicialSet.IntervalContraction
public import Colib.CategoryTheory.Sites.Simplicial.MappingCofiber
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseWeakEquivalence
public import Colib.Topology.Realization.HomotopyBridge
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# The reduced-cone contraction

Taking the maximum of the interval coordinate and the homotopy parameter
preserves each collapsed axis. It therefore descends along the actual
smash quotient and fixes its specified point.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- Pointwise maximum on the constant interval presheaf. -/
def presheafIntervalMax : (interval.{w} C) ⊗ (interval.{w} C) ⟶ (interval.{w} C) where
  app _ := SSet.intervalMax
  naturality _ _ _ := by simp [interval]

@[reassoc (attr := simp)]
theorem whiskerLeft_intervalEndpoint_zero_comp_max :
    ((interval.{w} C) ◁ intervalEndpoint C (1 : Fin 2)) ≫ presheafIntervalMax C =
      fst (interval.{w} C) (⊤_ (Cᵒᵖ ⥤ SSet.{w})) := by
  apply NatTrans.ext
  funext U
  change ((Δ[1] : SSet.{w}) ◁ (_ ≫ SSet.stdSimplex.δ (1 : Fin 2))) ≫
    SSet.intervalMax = fst _ _
  rw [whiskerLeft_comp, Category.assoc, SSet.whiskerLeft_δ_one_comp_intervalMax,
    whiskerLeft_fst]

@[reassoc (attr := simp)]
theorem whiskerLeft_intervalEndpoint_one_comp_max :
    ((interval.{w} C) ◁ intervalEndpoint C (0 : Fin 2)) ≫ presheafIntervalMax C =
      snd (interval.{w} C) (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ≫ intervalEndpoint C (0 : Fin 2) := by
  apply NatTrans.ext
  funext U
  change ((Δ[1] : SSet.{w}) ◁ (_ ≫ SSet.stdSimplex.δ (0 : Fin 2))) ≫
    SSet.intervalMax = snd _ _ ≫ (_ ≫ SSet.stdSimplex.δ (0 : Fin 2))
  rw [whiskerLeft_comp, Category.assoc, SSet.whiskerLeft_δ_zero_comp_intervalMax,
    whiskerLeft_snd_assoc]

@[reassoc (attr := simp)]
theorem intervalEndpoint_one_whiskerRight_comp_max :
    (intervalEndpoint C (0 : Fin 2) ▷ (interval.{w} C)) ≫ presheafIntervalMax C =
      fst (⊤_ (Cᵒᵖ ⥤ SSet.{w})) (interval.{w} C) ≫ intervalEndpoint C (0 : Fin 2) := by
  apply NatTrans.ext
  funext U
  change ((_ ≫ SSet.stdSimplex.δ (0 : Fin 2)) ▷ (Δ[1] : SSet.{w})) ≫
    SSet.intervalMax = fst _ _ ≫ (_ ≫ SSet.stdSimplex.δ (0 : Fin 2))
  rw [comp_whiskerRight, Category.assoc, SSet.δ_zero_whiskerRight_comp_intervalMax,
    whiskerRight_fst_assoc]

/-- The slice of the interval cylinder at a specified endpoint. -/
def intervalEndpointSlice (F : (Cᵒᵖ ⥤ SSet.{w})) (i : Fin 2) : F ⟶ F ⊗ (interval.{w} C) :=
  lift (𝟙 F) (terminal.from F ≫ intervalEndpoint C i)

@[reassoc]
theorem intervalEndpointSlice_naturality {F G : (Cᵒᵖ ⥤ SSet.{w})} (f : F ⟶ G) (i : Fin 2) :
    intervalEndpointSlice C F i ≫ (f ▷ (interval.{w} C)) = f ≫ intervalEndpointSlice C G i := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [intervalEndpointSlice]

@[reassoc (attr := simp)]
theorem intervalEndpointSlice_zero_comp_max :
    intervalEndpointSlice C (interval.{w} C) (1 : Fin 2) ≫ presheafIntervalMax C =
      𝟙 (interval.{w} C) := by
  rw [intervalEndpointSlice, ← lift_whiskerLeft, Category.assoc,
    whiskerLeft_intervalEndpoint_zero_comp_max, lift_fst]

@[reassoc (attr := simp)]
theorem intervalEndpointSlice_one_comp_max :
    intervalEndpointSlice C (interval.{w} C) (0 : Fin 2) ≫ presheafIntervalMax C =
      terminal.from (interval.{w} C) ≫ intervalEndpoint C (0 : Fin 2) := by
  rw [intervalEndpointSlice, ← lift_whiskerLeft, Category.assoc,
    whiskerLeft_intervalEndpoint_one_comp_max, lift_snd_assoc]

variable {C}

/-- The contraction on the product before passing to the smash quotient. -/
def reducedConeProductTrack (F : Cᵒᵖ ⥤ SSet.{w}) :
    (F ⨯ interval.{w} C) ⊗ interval.{w} C ⟶ F ⨯ interval.{w} C :=
  prod.lift (fst _ _ ≫ prod.fst) ((prod.snd ▷ (interval.{w} C)) ≫ presheafIntervalMax C)

namespace ReducedConeContraction

variable (X : PointedSimplicialPresheaf.{w} C)

/-- The first axis, with the interval coordinate at the last vertex. -/
abbrev tipAxis : X.right ⟶ X.right ⨯ (interval.{w} C) :=
  prod.lift (𝟙 _) (terminal.from X.right ≫ intervalEndpoint C (0 : Fin 2))

/-- The second axis, with the original presheaf coordinate at its point. -/
abbrev pointAxis : (interval.{w} C) ⟶ X.right ⨯ (interval.{w} C) :=
  prod.lift (terminal.from (interval.{w} C) ≫ X.hom) (𝟙 _)

@[reassoc]
theorem tipAxis_whisker_comp_track :
    (tipAxis X ▷ (interval.{w} C)) ≫ reducedConeProductTrack X.right = fst _ _ ≫ tipAxis X := by
  apply prod.hom_ext
  · simp [reducedConeProductTrack, tipAxis]
  · simp only [reducedConeProductTrack, Category.assoc, prod.lift_snd]
    rw [← comp_whiskerRight_assoc, prod.lift_snd, comp_whiskerRight_assoc,
      intervalEndpoint_one_whiskerRight_comp_max, whiskerRight_fst_assoc]

@[reassoc]
theorem pointAxis_whisker_comp_track :
    (pointAxis X ▷ (interval.{w} C)) ≫ reducedConeProductTrack X.right =
      presheafIntervalMax C ≫ pointAxis X := by
  apply prod.hom_ext
  · simp [reducedConeProductTrack, pointAxis]
  · simp only [reducedConeProductTrack, Category.assoc, prod.lift_snd]
    rw [← comp_whiskerRight_assoc, prod.lift_snd, id_whiskerRight, Category.id_comp,
      Category.comp_id]

@[reassoc]
theorem zero_comp_track :
    intervalEndpointSlice C (X.right ⨯ interval.{w} C) (1 : Fin 2) ≫
      reducedConeProductTrack X.right = 𝟙 _ := by
  apply prod.hom_ext
  · simp [reducedConeProductTrack, intervalEndpointSlice]
  · simp only [reducedConeProductTrack, Category.assoc, prod.lift_snd,
      intervalEndpointSlice_naturality_assoc, intervalEndpointSlice_zero_comp_max,
      Category.comp_id, Category.id_comp]

@[reassoc]
theorem one_comp_track :
    intervalEndpointSlice C (X.right ⨯ interval.{w} C) (0 : Fin 2) ≫
      reducedConeProductTrack X.right = prod.fst ≫ tipAxis X := by
  apply prod.hom_ext
  · simp [reducedConeProductTrack, intervalEndpointSlice, tipAxis]
  · simp only [reducedConeProductTrack, Category.assoc, prod.lift_snd,
      intervalEndpointSlice_naturality_assoc, intervalEndpointSlice_one_comp_max,
      terminal.comp_from_assoc]

local instance (J : Type*) [Category* J] [HasColimitsOfShape J (Type w)] :
    PreservesColimitsOfShape J (tensorRight (interval.{w} C)) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)

/-- The actual axes quotient used by the reduced cone is a pushout. -/
theorem isPushout :
    IsPushout (Under.axesToProduct X (basedInterval C)) (terminal.from _)
      (Under.toSmash X (basedInterval C)) (reducedCone X).hom :=
  IsPushout.of_hasPushout _ _

/-- The cylinder on the reduced cone is the whiskered axes pushout. -/
theorem cylinderIsPushout :
    IsPushout (Under.axesToProduct X (basedInterval C) ▷ (interval.{w} C))
      (terminal.from (X.right ⨿ interval.{w} C) ▷ interval.{w} C)
      (Under.toSmash X (basedInterval C) ▷ interval.{w} C)
      ((reducedCone X).hom ▷ (interval.{w} C)) :=
  (tensorRight (interval.{w} C)).map_isPushout (isPushout X)

theorem track_axes_compatibility :
    (Under.axesToProduct X (basedInterval C) ▷ (interval.{w} C)) ≫
        (reducedConeProductTrack X.right ≫ Under.toSmash X (basedInterval C)) =
      (terminal.from (X.right ⨿ (interval.{w} C)) ▷ (interval.{w} C)) ≫
        (fst (⊤_ (Cᵒᵖ ⥤ SSet.{w})) (interval.{w} C) ≫ (reducedCone X).hom) := by
  let q : X.right ⨯ interval.{w} C ⟶ (reducedCone X).right :=
    Under.toSmash X (basedInterval C)
  have hTip : tipAxis X ≫ q = terminal.from X.right ≫ (reducedCone X).hom :=
    Under.leftAxis_toSmash X (basedInterval C)
  have hPoint : pointAxis X ≫ q = terminal.from (interval.{w} C) ≫ (reducedCone X).hom :=
    Under.rightAxis_toSmash X (basedInterval C)
  change ((coprod.desc (tipAxis X) (pointAxis X)) ▷ interval.{w} C) ≫
    (reducedConeProductTrack X.right ≫ q) = _
  apply BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit
      (tensorRight (interval.{w} C)) X.right (interval.{w} C))
  · change (coprod.inl ▷ (interval.{w} C)) ≫ _ = (coprod.inl ▷ (interval.{w} C)) ≫ _
    simp only [← comp_whiskerRight_assoc, coprod.inl_desc, tipAxis_whisker_comp_track_assoc,
      hTip, whiskerRight_fst_assoc, terminal.comp_from_assoc]
  · change (coprod.inr ▷ (interval.{w} C)) ≫ _ = (coprod.inr ▷ (interval.{w} C)) ≫ _
    simp only [← comp_whiskerRight_assoc, coprod.inr_desc, pointAxis_whisker_comp_track_assoc,
      hPoint, whiskerRight_fst_assoc, terminal.comp_from_assoc]

end ReducedConeContraction

open ReducedConeContraction

/-- The contraction of the actual reduced cone, descended from interval maximum. -/
def reducedConeCylinder (X : PointedSimplicialPresheaf.{w} C) :
    (reducedCone X).right ⊗ (interval.{w} C) ⟶ (reducedCone X).right :=
  (cylinderIsPushout X).desc (reducedConeProductTrack X.right ≫ Under.toSmash X (basedInterval C))
    (fst (⊤_ (Cᵒᵖ ⥤ SSet.{w})) (interval.{w} C) ≫ (reducedCone X).hom) (track_axes_compatibility X)

@[reassoc]
theorem toSmash_whisker_comp_reducedConeCylinder (X : PointedSimplicialPresheaf.{w} C) :
    (Under.toSmash X (basedInterval C) ▷ (interval.{w} C)) ≫ reducedConeCylinder X =
      reducedConeProductTrack X.right ≫ Under.toSmash X (basedInterval C) :=
  (cylinderIsPushout X).inl_desc _ _ _

/-- The cone point stays fixed throughout the contraction. -/
@[reassoc]
theorem reducedCone_point_whisker_comp_cylinder (X : PointedSimplicialPresheaf.{w} C) :
    ((reducedCone X).hom ▷ (interval.{w} C)) ≫ reducedConeCylinder X =
      fst (⊤_ (Cᵒᵖ ⥤ SSet.{w})) (interval.{w} C) ≫ (reducedCone X).hom :=
  (cylinderIsPushout X).inr_desc _ _ _

@[reassoc]
theorem reducedConeCylinder_zero (X : PointedSimplicialPresheaf.{w} C) :
    intervalEndpointSlice C (reducedCone X).right (1 : Fin 2) ≫ reducedConeCylinder X = 𝟙 _ := by
  apply (isPushout X).hom_ext
  · let q : X.right ⨯ interval.{w} C ⟶ (reducedCone X).right :=
      Under.toSmash X (basedInterval C)
    have hq : (q ▷ interval.{w} C) ≫ reducedConeCylinder X = reducedConeProductTrack X.right ≫ q :=
      toSmash_whisker_comp_reducedConeCylinder X
    change q ≫ _ = q ≫ _
    rw [← intervalEndpointSlice_naturality_assoc, hq, ← Category.assoc, zero_comp_track]
    simp
  · rw [← intervalEndpointSlice_naturality_assoc, reducedCone_point_whisker_comp_cylinder]
    simp [intervalEndpointSlice]

@[reassoc]
theorem reducedConeCylinder_one (X : PointedSimplicialPresheaf.{w} C) :
    intervalEndpointSlice C (reducedCone X).right (0 : Fin 2) ≫ reducedConeCylinder X =
      terminal.from (reducedCone X).right ≫ (reducedCone X).hom := by
  apply (isPushout X).hom_ext
  · let q : X.right ⨯ interval.{w} C ⟶ (reducedCone X).right :=
      Under.toSmash X (basedInterval C)
    have hq : (q ▷ interval.{w} C) ≫ reducedConeCylinder X = reducedConeProductTrack X.right ≫ q :=
      toSmash_whisker_comp_reducedConeCylinder X
    have hTip : tipAxis X ≫ q = terminal.from X.right ≫ (reducedCone X).hom :=
      Under.leftAxis_toSmash X (basedInterval C)
    change q ≫ _ = q ≫ _
    rw [← intervalEndpointSlice_naturality_assoc, hq, ← Category.assoc, one_comp_track]
    simp only [Category.assoc, hTip, terminal.comp_from_assoc]
  · rw [← intervalEndpointSlice_naturality_assoc, reducedCone_point_whisker_comp_cylinder]
    have h : terminal.from (⊤_ (Cᵒᵖ ⥤ SSet.{w})) = 𝟙 _ := terminalIsTerminal.hom_ext _ _
    simp [intervalEndpointSlice, h]

section Transport

variable (F : (Cᵒᵖ ⥤ SSet.{w}) ⥤ SSet.{w})
  (e : (Functor.const Cᵒᵖ : SSet.{w} ⥤ _) ⋙ F ≅ 𝟭 _)

@[reassoc]
theorem map_intervalEndpoint_comp_constIso (i : Fin 2) :
    F.map (intervalEndpoint C i) ≫ (e.app (Δ[1] : SSet.{w})).hom =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ i := by
  let p : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ (Functor.const Cᵒᵖ).obj (Δ[0] : SSet.{w}) :=
    (Functor.isTerminalConst Cᵒᵖ SSet.stdSimplex.isTerminalObj₀).from _
  have hp : intervalEndpoint C i = p ≫ (Functor.const Cᵒᵖ).map (SSet.stdSimplex.δ i) := rfl
  have h := e.hom.naturality (SSet.stdSimplex.δ i)
  change F.map ((Functor.const Cᵒᵖ).map (SSet.stdSimplex.δ i)) ≫
    (e.app (Δ[1] : SSet.{w})).hom = (e.app (Δ[0] : SSet.{w})).hom ≫
      SSet.stdSimplex.δ i at h
  rw [hp, Functor.map_comp, Category.assoc, h, ← Category.assoc]
  exact congrArg (fun a => a ≫ SSet.stdSimplex.δ i) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

variable [PreservesFiniteProducts F]

/-- A finite-product-preserving functor with its comparison on constants
takes the presheaf cylinder to the native simplicial cylinder. -/
def intervalCylinderComparison (Y : Cᵒᵖ ⥤ SSet.{w}) :
    F.obj (Y ⊗ interval.{w} C) ≅ F.obj Y ⊗ Δ[1] :=
  asIso (prodComparison F Y (interval.{w} C)) ≪≫
    whiskerLeftIso (F.obj Y) (e.app (Δ[1] : SSet.{w}))

@[reassoc (attr := simp)]
theorem intervalCylinderComparison_hom_fst (Y : Cᵒᵖ ⥤ SSet.{w}) :
    (intervalCylinderComparison F e Y).hom ≫ fst _ _ = F.map (fst Y (interval.{w} C)) := by
  simp [intervalCylinderComparison]

@[reassoc (attr := simp)]
theorem intervalCylinderComparison_hom_snd (Y : Cᵒᵖ ⥤ SSet.{w}) :
    (intervalCylinderComparison F e Y).hom ≫ snd _ _ =
      F.map (snd Y (interval.{w} C)) ≫ (e.app (Δ[1] : SSet.{w})).hom := by
  simp [intervalCylinderComparison]

theorem map_intervalEndpointSlice_comp_comparison (Y : Cᵒᵖ ⥤ SSet.{w}) (i : Fin 2) :
    F.map (intervalEndpointSlice C Y i) ≫ (intervalCylinderComparison F e Y).hom =
      lift (𝟙 (F.obj Y)) (SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ i) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, intervalCylinderComparison_hom_fst, ← Functor.map_comp,
      intervalEndpointSlice, lift_fst, Functor.map_id]
  · rw [Category.assoc, intervalCylinderComparison_hom_snd, ← Functor.map_comp_assoc,
      intervalEndpointSlice, lift_snd, Functor.map_comp, Category.assoc,
      map_intervalEndpoint_comp_constIso, lift_snd, ← Category.assoc]
    exact congrArg (fun a => a ≫ SSet.stdSimplex.δ i) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- The actual transported simplicial homotopy from the identity to the point collapse. -/
def mapReducedConeHomotopy (X : PointedSimplicialPresheaf.{w} C) :
    SSet.Homotopy (𝟙 (F.obj (reducedCone X).right))
      (F.map (terminal.from (reducedCone X).right) ≫ F.map (reducedCone X).hom) where
  h := (intervalCylinderComparison F e (reducedCone X).right).inv ≫
    F.map (reducedConeCylinder X)
  h₀ := by
    have hi := map_intervalEndpointSlice_comp_comparison F e (reducedCone X).right (1 : Fin 2)
    rw [SSet.stdSimplex.δ_one_eq_const, SSet.comp_const] at hi
    change _ = SSet.ι₀ at hi
    change SSet.ι₀ ≫ _ = 𝟙 _
    rw [← hi, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
      reducedConeCylinder_zero, Functor.map_id]
  h₁ := by
    have hi := map_intervalEndpointSlice_comp_comparison F e (reducedCone X).right (0 : Fin 2)
    rw [SSet.stdSimplex.δ_zero_eq_const, SSet.comp_const] at hi
    change _ = SSet.ι₁ at hi
    change SSet.ι₁ ≫ _ = F.map (terminal.from (reducedCone X).right) ≫ F.map (reducedCone X).hom
    rw [← hi, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
      reducedConeCylinder_one, Functor.map_comp]
  rel := by ext n z; exact z.1.property.elim

include e in
/-- The actual cone collapse realizes to a homotopy equivalence after transport. -/
theorem isRealizationWeakEquivalence_map_reducedConeToPoint
    (X : PointedSimplicialPresheaf.{w} C) :
    SSet.IsRealizationWeakEquivalence (F.map (toPoint C (reducedCone X)).right) := by
  change SSet.IsRealizationWeakEquivalence (F.map (terminal.from (reducedCone X).right))
  refine Topology.isWeakHomotopyEquivalence_of_homotopyEquiv
    { toFun := (SSet.toTop.map (F.map (terminal.from (reducedCone X).right))).hom
      invFun := (SSet.toTop.map (F.map (reducedCone X).hom)).hom
      left_inv := ?_
      right_inv := ?_ }
  · have h := (SSet.realizationSimplicialHomotopy (mapReducedConeHomotopy F e X)).symm
    exact ⟨by simpa only [Functor.map_id, Functor.map_comp, TopCat.hom_id, TopCat.hom_comp]
      using h⟩
  · have h : (reducedCone X).hom ≫ terminal.from (reducedCone X).right = 𝟙 _ :=
      terminalIsTerminal.hom_ext _ _
    have h' := congrArg (fun g => (SSet.toTop.map (F.map g)).hom) h
    simp only [Functor.map_comp, Functor.map_id, TopCat.hom_comp, TopCat.hom_id] at h'
    rw [h']

end Transport

/-- The point collapse of the reduced cone is an objectwise realization weak equivalence. -/
theorem objectwiseWeakEquivalences_reducedConeToPoint
    (X : PointedSimplicialPresheaf.{w} C) :
    objectwiseWeakEquivalences C (toPoint C (reducedCone X)) :=
  fun U => isRealizationWeakEquivalence_map_reducedConeToPoint
    ((CategoryTheory.evaluation Cᵒᵖ SSet).obj U) (Iso.refl _) X

/-- Filtered colimits of simplicial sets commute with finite limits degreewise. -/
instance _root_.SSet.instAB5OfSize : AB5OfSize.{w, w} (SSet.{w}) where
  ofShape _ _ _ := ⟨{ preservesFiniteLimits _ := inferInstance }⟩

/-- The cone collapse induces a realization weak equivalence at the actual site point. -/
theorem isRealizationWeakEquivalence_fiberAtPoint_reducedConeToPoint
    [LocallySmall.{w} C] {J : GrothendieckTopology C} (Φ : J.Point.{w})
    (X : PointedSimplicialPresheaf.{w} C) :
    SSet.IsRealizationWeakEquivalence
      ((fiberAtPoint C Φ).map (toPoint C (reducedCone X))) :=
  isRealizationWeakEquivalence_map_reducedConeToPoint
    (Φ.presheafFiber (A := SSet.{w})) (Sites.constantPresheafFiberNatIso Φ) X

end CategoryTheory.PointedSimplicialPresheaf
