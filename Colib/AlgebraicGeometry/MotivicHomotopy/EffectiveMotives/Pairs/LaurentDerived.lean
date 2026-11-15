/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.LaurentCochain

/-! # Derived comparison with the original Laurent quotient of a pair -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (LargePresheaves k)] [HasDerivedCategory.{w'} (LargeSheaves k)]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "NST" => LargeSheaves k
local notation "F" => parameterTensorFunctor G
local notation "a" => nisnevichSheafify k
local notation "Q" => (DerivedCategory.Q : CochainComplex NST ℤ ⥤ DerivedCategory NST)

/-- The canonical abelian structure on sheaves with transfers. -/
local instance laurentDerivedAbelian : Abelian NST := SheafWithTransfers.abelian k

variable {U X : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)
  [IsOpenImmersion (torusCylinder.map j).left]

local notation "J" => Arrow.mk j
set_option quotPrecheck false in
local notation "K" => (projectivePairDerived k).obj J

set_option maxHeartbeats 750000 in
-- Identify the ambient derived objects after the actual cone augmentation.
/-- The unreduced derived Laurent tensor is the original Laurent quotient. -/
@[no_expose]
def projectiveLaurentPairComparison :
    (projectiveTorusTensorToDerivedMinus k).obj K ≅
      (singleTransferSheafMinus k).obj
        ((transferPairCokernelFunctor k).obj ((laurentPair k).obj J)) := by
  let e := projectivePairTermwiseModelIso k F J
  let f := laurentCochainAugmentation k J
  let u := laurentCochainComparison k J
  letI : IsIso ((Q).map (u.hom ≫ f)) := by
    let : IsIso ((Q).map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso NST f).2
      (quasiIso_laurentCochainAugmentation k j)
    rw [(Q).map_comp]
    infer_instance
  exact ObjectProperty.isoMk _ (e ≪≫ asIso ((Q).map (u.hom ≫ f)))

set_option maxHeartbeats 600000 in
-- Evaluate the lifted isomorphism on the literal terms of the ambient comparison.
/-- The ambient morphism of the Laurent comparison is termwise computation
followed by the image of the original cone augmentation. -/
theorem projectiveLaurentPairComparison_hom_hom :
    let e := projectivePairTermwiseModelIso k F J
    let l := laurentCochainComparison k J
    let f := laurentCochainAugmentation k J
    (projectiveLaurentPairComparison k j).hom.hom = e.hom ≫ (Q).map (l.hom ≫ f) := by
  intro e l f
  unfold projectiveLaurentPairComparison
  rfl

end AlgebraicGeometry.MotivicHomotopy
