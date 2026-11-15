/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineCover
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-! # Excision for the original relative Laurent pair -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

private def effectiveCokernelExcisionIso {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [HasZeroMorphisms D] [HasCokernels D] (R : C ⥤ D) (F : D ⥤ E)
    {a b : Arrow C} (f : a ⟶ b)
    (h : IsPushout (R.map a.hom) (R.map f.left) (R.map f.right) (R.map b.hom)) :
    let P := (R.mapArrow ⋙ coker D) ⋙ F
    { e : P.obj a ≅ P.obj b // e.hom = P.map f } := by
  intro P
  let q := cokernel.map (R.map a.hom) (R.map b.hom) (R.map f.left) (R.map f.right) h.w
  exact ⟨F.mapIso (@asIso _ _ _ _ q (isIso_cokernel_map_of_isPushout h)), rfl⟩

variable (k : Type u) [Field k]

variable {U X W : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)
  (i : affineLineCylinder.obj U ⟶ W) (l : torusCylinder.obj X ⟶ W)
  (v : W ⟶ affineLineCylinder.obj X) [IsOpenImmersion v.left]
  (hi : i ≫ v = affineLineCylinder.map j) (hl : l ≫ v = openInclusion.app X)
  [IsOpenImmersion i.left] [IsOpenImmersion l.left]

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option maxHeartbeats 900000 in
-- Identify the indicated arrow and its reflected quotient before forming the isomorphism.
/-- The open-cover comparison together with its component on the original pair morphism. -/
@[no_expose]
def relativeLineLaurentComparisonData
    (hpull : (relativeLineOpenCoverSquare k j i l v hi hl).IsPullback)
    (hunion : Set.range i.left ∪ Set.range l.left = Set.univ) :=
  effectiveCokernelExcisionIso (smoothTransferRepresentable k) (effectiveTransferSheaf k)
    (relativeLineLaurentArrow k j i l v hi hl)
    (relativeLineTransferPushout k j i l v hi hl hpull hunion)

set_option maxHeartbeats 1300000 in
-- Keep the actual pair objects as the domain and codomain.
/-- The open-cover comparison identifies the first term of the nested
triangle with the motive of the actual relative Laurent pair. -/
def relativeLineLaurentComparison
    (hpull : (relativeLineOpenCoverSquare k j i l v hi hl).IsPullback)
    (hunion : Set.range i.left ∪ Set.range l.left = Set.univ) :
    let P := effectivePairMotiveFunctor k
    P.obj (Arrow.mk (torusCylinder.map j)) ≅ P.obj (Arrow.mk i) :=
  (relativeLineLaurentComparisonData k j i l v hi hl hpull hunion).val

end AlgebraicGeometry.MotivicHomotopy
