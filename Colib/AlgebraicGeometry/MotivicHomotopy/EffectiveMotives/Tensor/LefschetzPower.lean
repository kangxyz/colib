/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeLefschetz
public import Colib.CategoryTheory.Triangulated.Stabilization.Stages
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Powers of the effective Lefschetz tensor -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

/-- The canonical additive sheafification on the Nisnevich correspondence site. -/
local instance lefschetzPowerCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The canonical additive sheafification on the smooth Nisnevich site. -/
local instance lefschetzPowerSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "E" => EffectiveMotivesMinus k
local notation "B" => SmoothSite.base S
local notation "M" => effectiveSmoothMotive k
local notation "L" => effectiveLefschetzTwistFunctor k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The canonical abelian structure on sheaves with transfers. -/
local instance lefschetzPowerAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The effective tensor carries the signed convolution of transfer complexes. -/
local instance lefschetzPowerMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory θ

/-- The symmetry moves the Lefschetz factor past the tensor input. -/
local instance lefschetzPowerSymmetric : SymmetricCategory E :=
  effectiveSignedConvolutionSymmetricCategory θ

/-- The Lefschetz power of the base motive acts by the corresponding original
iterate of the effective Lefschetz twist. -/
def effectiveLefschetzPowerTensorIso (A : E) (c : ℕ) :
    (Stabilization.iterate L c).obj ((M).obj B) ⊗ A ≅ (Stabilization.iterate L c).obj A := by
  let K := effectiveLefschetzMotive k
  let e := effectiveLefschetzTensorIso k
  induction c with
  | zero =>
    exact (tensorRight A).mapIso (effectiveSignedConvolutionUnitIso θ).symm ≪≫ λ_ A
  | succ c h =>
    let C := (Stabilization.iterate L c).obj ((M).obj B)
    exact (tensorRight A).mapIso (e.app C).symm ≪≫
      α_ C K A ≪≫ (tensorLeft C).mapIso (β_ K A) ≪≫ (α_ C A K).symm ≪≫
      e.app (C ⊗ A) ≪≫ (L).mapIso h

set_option Elab.async false in
set_option maxHeartbeats 900000 in
-- Move the morphism through the original unit, associativity and symmetry comparisons.
/-- The Lefschetz-power tensor comparison is natural in the effective motive. -/
@[reassoc]
theorem effectiveLefschetzPowerTensorIso_naturality {A A' : E} (f : A ⟶ A') (c : ℕ) :
    ((Stabilization.iterate L c).obj ((M).obj B) ◁ f) ≫
        (effectiveLefschetzPowerTensorIso k A' c).hom =
      (effectiveLefschetzPowerTensorIso k A c).hom ≫ (Stabilization.iterate L c).map f := by
  let K := effectiveLefschetzMotive k
  let e : tensorRight K ≅ L := effectiveLefschetzTensorIso k
  induction c with
  | zero =>
    let d : (M).obj B ⟶ 𝟙_ E := (effectiveSignedConvolutionUnitIso θ).inv
    have hex : (((M).obj B) ◁ f) ≫ (d ▷ A') = (d ▷ A) ≫ ((𝟙_ E) ◁ f) :=
      whisker_exchange d f
    change (((M).obj B) ◁ f) ≫ (d ▷ A') ≫ (λ_ A').hom = ((d ▷ A) ≫ (λ_ A).hom) ≫ f
    calc
      _ = ((d ▷ A) ≫ ((𝟙_ E) ◁ f)) ≫ (λ_ A').hom :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (λ_ A').hom) hex)
      _ = _ := by rw [Category.assoc, leftUnitor_naturality, Category.assoc]
  | succ c ih =>
    let D := (Stabilization.iterate L c).obj ((M).obj (SmoothSite.base S))
    let a := effectiveLefschetzPowerTensorIso k A c
    let b := effectiveLefschetzPowerTensorIso k A' c
    have hex : ((L).obj D ◁ f) ≫ (e.inv.app D ▷ A') =
        (e.inv.app D ▷ A) ≫ ((D ⊗ K) ◁ f) := whisker_exchange (e.inv.app D) f
    have hβ : (D ◁ (K ◁ f)) ≫ (D ◁ (β_ K A').hom) =
        (D ◁ (β_ K A).hom) ≫ (D ◁ (f ▷ K)) := by
      rw [← whiskerLeft_comp, braiding_naturality_right, whiskerLeft_comp]
    have he : ((D ◁ f) ▷ K) ≫ e.hom.app (D ⊗ A') =
        e.hom.app (D ⊗ A) ≫ (L).map (D ◁ f) := e.hom.naturality (D ◁ f)
    change ((L).obj D ◁ f) ≫
        (e.inv.app D ▷ A') ≫ (α_ D K A').hom ≫ D ◁ (β_ K A').hom ≫
        (α_ D A' K).inv ≫ e.hom.app (D ⊗ A') ≫ (L).map b.hom =
      ((e.inv.app D ▷ A) ≫ (α_ D K A).hom ≫ D ◁ (β_ K A).hom ≫
        (α_ D A K).inv ≫ e.hom.app (D ⊗ A) ≫ (L).map a.hom) ≫
          (L).map ((Stabilization.iterate L c).map f)
    let q := (α_ D K A').hom ≫ D ◁ (β_ K A').hom ≫ (α_ D A' K).inv ≫
      e.hom.app (D ⊗ A') ≫ (L).map b.hom
    refine ((Category.assoc _ _ q).symm.trans (congrArg (· ≫ q) hex)).trans ?_
    dsimp only [q]
    simp only [Category.assoc]
    rw [associator_naturality_right_assoc, reassoc_of% hβ,
      associator_inv_naturality_middle_assoc, reassoc_of% he]
    have htail : (L).map (D ◁ f) ≫ (L).map b.hom =
        (L).map a.hom ≫ (L).map ((Stabilization.iterate L c).map f) :=
      ((L).map_comp (D ◁ f) b.hom).symm.trans
        (((L).congr_map ih).trans ((L).map_comp a.hom ((Stabilization.iterate L c).map f)))
    change (e.inv.app D ▷ A) ≫ (α_ D K A).hom ≫ D ◁ (β_ K A).hom ≫
        (α_ D A K).inv ≫ e.hom.app (D ⊗ A) ≫ ((L).map (D ◁ f) ≫ (L).map b.hom) =
      (e.inv.app D ▷ A) ≫ (α_ D K A).hom ≫ D ◁ (β_ K A).hom ≫
        (α_ D A K).inv ≫ e.hom.app (D ⊗ A) ≫
          ((L).map a.hom ≫ (L).map ((Stabilization.iterate L c).map f))
    exact congrArg (fun t ↦ (e.inv.app D ▷ A) ≫ (α_ D K A).hom ≫ D ◁ (β_ K A).hom ≫
      (α_ D A K).inv ≫ e.hom.app (D ⊗ A) ≫ t) htail

end AlgebraicGeometry.MotivicHomotopy
