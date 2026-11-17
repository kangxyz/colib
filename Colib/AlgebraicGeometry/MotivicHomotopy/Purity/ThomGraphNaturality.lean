/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothProduct
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ThomGraphBasic
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Naturality of the supported Thom graph under maps of pairs -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private theorem graph_paste_tensor {C : Type*} [Category* C] (F : C ⥤ C)
    {A A' B B' K : C} (g : A ⟶ A') (a : A ⟶ B) (a' : A' ⟶ B') (d : B ⟶ B')
    (e : F.obj A ≅ B) (e' : F.obj A' ≅ B') (t : A' ⟶ K)
    (h : CommSq g a a' d) (h' : CommSq (F.map g) e.hom e'.hom d) :
    g ≫ a' ≫ e'.inv ≫ F.map t = a ≫ e.inv ≫ F.map (g ≫ t) := by
  have h₀ := (h.vert_comp h'.vert_inv).w_assoc (F.map t)
  simpa only [Category.assoc, F.map_comp] using h₀

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] thomGraphBasicCorSheafify thomGraphBasicSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "E" => EffectiveMotivesMinus k
local notation "M" => effectiveSmoothMotive k
local notation "Φ" => effectivePairMotiveFunctor k

attribute [local instance] thomGraphBasicBaseNoetherian thomGraphBasicAbelian thomGraphBasicMonoidal

attribute [local irreducible] effectivePairThomGraph
attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

set_option maxHeartbeats 1800000 in
-- The product comparison is on the original smooth pair functors.
/-- Applying the class after a map of pairs uses its actual composition with that map. -/
theorem effectivePairThomGraph_naturality {A V A' V' Y : Sm}
    {j : A ⟶ V} {j' : A' ⟶ V'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (f : Arrow.mk j ⟶ Arrow.mk j') (p : V ⟶ Y) (p' : V' ⟶ Y) (h : f.right ≫ p' = p)
    {K : E} (t : effectivePairMotive k j' ⟶ K) :
    (Φ).map f ≫ effectivePairThomGraph k (j := j') p' (K := K) t =
      effectivePairThomGraph k (j := j) p (K := K) ((Φ).map f ≫ t) := by
  let e := effectivePairProductRightIso k j Y
  let e' := effectivePairProductRightIso k j' Y
  let d := (Φ).map ((parameterProduct Y).mapArrow.map f)
  let g : effectivePairMotive k j ⟶ effectivePairMotive k j' := (Φ).map f
  let F : E ⥤ E := tensorRight ((M).obj Y)
  let a := pairProductGraph j p
  let a' := pairProductGraph j' p'
  have h₁ : CommSq f a a' ((parameterProduct Y).mapArrow.map f) :=
    ⟨pairProductGraph_naturality f p p' h⟩
  have h₂ : CommSq g ((Φ).map a) ((Φ).map a') d := h₁.map (Φ)
  have h₃ : CommSq (F.map g) e.hom e'.hom d :=
    ⟨effectivePairProductRightIso_naturality k f Y⟩
  unfold effectivePairThomGraph
  exact graph_paste_tensor F g ((Φ).map a) ((Φ).map a') d e e' t h₂ h₃

end AlgebraicGeometry.MotivicHomotopy
