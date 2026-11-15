/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SmoothMotive
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.RepresentableTorusUnit
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Exactness
import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Normalization

/-! # The reduced torus and Lefschetz objects -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => SmoothSite.base S
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "M" => effectiveSmoothMotive k
local notation "D" => EffectiveMotivesMinus k

/-- The reduced torus tensor on a smooth motive is a retract of the motive
of the actual torus product. -/
def effectiveReducedTorusTensorRepresentableRetract (X : Cor k) :
    Retract ((effectiveReducedTorusTensorFunctor k).obj ((effectiveMotive k).obj X))
      ((effectiveMotive k).obj ((Cor.parameterProduct
        (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).obj X)) := by
  let Q := singularEffectiveMotiveFunctor k
  let comparison := effectiveReducedTorusTensorRepresentableIso k X
  let i := torusCancellationCoefficientSection k X
  let r := toTorusCancellationCoefficients k X
  refine ⟨comparison.hom ≫ Q.map i, Q.map r ≫ comparison.inv, ?_⟩
  change (comparison.hom ≫ Q.map i) ≫ (Q.map r ≫ comparison.inv) = 𝟙 _
  rw [Category.assoc, ← Category.assoc (Q.map i), ← Q.map_comp,
    torusCancellationCoefficientSection_π, Q.map_id, Category.id_comp, Iso.hom_inv_id]

/-- The actual reduced quotient and its section cut out the complement of
the graph of the torus projection followed by the unit section. -/
theorem effectiveReducedTorusTensorRepresentableRetract_projection_inclusion (X : Cor k) :
    (effectiveReducedTorusTensorRepresentableRetract k X).r ≫
      (effectiveReducedTorusTensorRepresentableRetract k X).i =
      𝟙 _ - (effectiveMotive k).map (torusUnitProjector k X) := by
  let Q := singularEffectiveMotiveFunctor k
  let e := effectiveReducedTorusTensorRepresentableIso k X
  let : (singularSheafCochainFunctor k 0).Additive := by
    unfold singularSheafCochainFunctor singularCochainFunctor
    infer_instance
  let : Q.Additive := ⟨by
    intro U V f g
    apply (effectiveMotivesMinusToDerived k).map_injective
    exact ((singularSheafCochainFunctor k 0) ⋙ DerivedCategory.Q).map_add⟩
  change (Q.map (toTorusCancellationCoefficients k X) ≫ e.inv) ≫
    e.hom ≫ Q.map (torusCancellationCoefficientSection k X) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Q.map_comp,
    toTorusCancellationCoefficients_section, Q.map_sub, Q.map_id]
  rfl

/-- The native reduced torus tensor of the smooth base motive. -/
abbrev effectiveReducedTorusMotive :
    D :=
  (effectiveReducedTorusTensorFunctor k).obj ((M).obj B)

/-- The product with the base in the first slot projects isomorphically to the torus. -/
abbrev torusBaseProduct : SmoothSite.product B G ≅ G where
  hom := SmoothSite.productSnd B G
  inv := SmoothSite.productLift (toBase G) (𝟙 G)
  hom_inv_id := by
    apply SmoothSite.product_hom_ext
    · rw [Category.assoc, SmoothSite.productLift_fst, comp_toBase, Category.id_comp]
      exact MorphismProperty.Over.Hom.ext (Category.comp_id _)
    · simp
  inv_hom_id := SmoothSite.productLift_snd _ _

/-- The original section of the reduced torus projection. -/
def torusReducedInclusion : effectiveReducedTorusMotive k ⟶ (M).obj G :=
  (effectiveReducedTorusTensorRepresentableRetract k (Cor.mk B)).i ≫
    (M).map (torusBaseProduct (k := k)).hom

/-- The projection from the native torus motive to the actual reduced torus tensor of the base. -/
def torusReducedProjection : (M).obj G ⟶ effectiveReducedTorusMotive k :=
  (M).map (torusBaseProduct (k := k)).inv ≫
    (effectiveReducedTorusTensorRepresentableRetract k (Cor.mk B)).r

/-- The projection retracts its original section. -/
theorem torusReducedInclusion_projection :
    torusReducedInclusion k ≫ torusReducedProjection k = 𝟙 _ := by
  let t := torusBaseProduct (k := k)
  let r := effectiveReducedTorusTensorRepresentableRetract k (Cor.mk B)
  change (r.i ≫ (M).map t.hom) ≫ (M).map t.inv ≫ r.r = 𝟙 _
  rw [Category.assoc, ← (M).map_comp_assoc, Iso.hom_inv_id, (M).map_id, Category.id_comp,
    r.retract]

/-- The ambient projector is the identity minus the unit-section projector. -/
theorem torusReducedProjection_inclusion :
    torusReducedProjection k ≫ torusReducedInclusion k =
      𝟙 ((M).obj G) - (M).map (toBase G) ≫ (M).map (SmoothSite.torusOne S) := by
  let X := Cor.mk B
  let t := torusBaseProduct (k := k)
  have h := effectiveReducedTorusTensorRepresentableRetract_projection_inclusion k X
  have hpoint : t.inv ≫
      (SmoothSite.productFst B G ≫ unitSection.app B) ≫ t.hom =
      toBase G ≫ SmoothSite.torusOne S := by
    change SmoothSite.productLift (toBase G) (𝟙 G) ≫
      (SmoothSite.productFst B G ≫
        SmoothSite.productLift (𝟙 B) (toBase B ≫ SmoothSite.torusOne S)) ≫
      SmoothSite.productSnd B G = _
    simp only [Category.assoc, SmoothSite.productLift_fst_assoc, SmoothSite.productLift_snd]
    rw [← Category.assoc, comp_toBase]
  change ((M).map t.inv ≫ (effectiveReducedTorusTensorRepresentableRetract k X).r) ≫
    (effectiveReducedTorusTensorRepresentableRetract k X).i ≫ (M).map t.hom = _
  have hm : (effectiveMotive k).map (torusUnitProjector k X) =
      (M).map (SmoothSite.productFst B G ≫ unitSection.app B) := by
    rw [torusUnitProjector_eq_graph]
    rfl
  have hinv : (M).map t.inv ≫ (M).map t.hom = 𝟙 _ := by
    rw [← (M).map_comp, t.inv_hom_id, (M).map_id]
  rw [Category.assoc, ← Category.assoc
    (effectiveReducedTorusTensorRepresentableRetract k X).r, h, hm, Preadditive.sub_comp,
    Category.id_comp, Preadditive.comp_sub, hinv, ← (M).map_comp, ← (M).map_comp, hpoint,
    (M).map_comp]

/-- The native reduced torus is the retract defined by the unit-section projector. -/
def torusReducedRetract : Retract (effectiveReducedTorusMotive k) ((M).obj G) :=
  ⟨torusReducedInclusion k, torusReducedProjection k, torusReducedInclusion_projection k⟩

/-- The Lefschetz object is the reduced torus motive shifted by one. -/
abbrev effectiveLefschetzMotive : D := (effectiveReducedTorusMotive k)⟦(1 : ℤ)⟧

/-- Tensoring by one effective Lefschetz factor, with the signed cochain shift. -/
abbrev effectiveLefschetzTwistFunctor : EffectiveMotivesMinus k ⥤ EffectiveMotivesMinus k :=
  effectiveReducedTorusTensorFunctor k ⋙ shiftFunctor (EffectiveMotivesMinus k) (1 : ℤ)

end AlgebraicGeometry.MotivicHomotopy
