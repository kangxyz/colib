/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.LaurentDerived
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ReducedTorusComparison
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The actual reduced Laurent summand of a relative motive

On the literal projective cone for an open inclusion, termwise Laurent
product gives the Laurent pair. Its complementary projector is the
original reduced torus tensor, identified by the existing adjunction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "NST" => LargeSheaves k
local notation "F" => parameterTensorFunctor G
local notation "a" => nisnevichSheafify k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance laurentRetractAbelian : Abelian NST := SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (LargePresheaves k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]

local notation "Q" => (DerivedCategory.Q : CochainComplex NST ℤ ⥤ DerivedCategory NST)

variable {U X : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)

local notation "J" => Arrow.mk j
set_option quotPrecheck false in
local notation "K" => (projectivePairDerived k).obj J

/-- The native coefficient projector on the unreduced derived Laurent tensor. -/
abbrev projectiveLaurentPairProjector :
    (projectiveTorusTensorToDerivedMinus k).obj K ⟶ (projectiveTorusTensorToDerivedMinus k).obj K :=
  (derivedNisnevichSheafification k).map ((projectiveCoefficientNatTrans k
    (laurentTensorProjector k)).app K)

private theorem map_comp_eq {C D : Type*} [Category* C] [Category* D] (M₀ : C ⥤ D)
    {A B B' D₀ : C} {f : A ⟶ B} {g : B ⟶ D₀} {f' : A ⟶ B'} {g' : B' ⟶ D₀}
    (h : f ≫ g = f' ≫ g') : M₀.map f ≫ M₀.map g = M₀.map f' ≫ M₀.map g' :=
  (M₀.map_comp _ _).symm.trans ((M₀.congr_map h).trans (M₀.map_comp _ _))

section Unreduced

variable [IsOpenImmersion (torusCylinder.map j).left]

set_option maxHeartbeats 850000 in
-- Identify the reflected projector after applying the original cochain comparison.
/-- The projective tensor comparison is equivariant for the actual Laurent projector. -/
theorem projectiveLaurentPairComparison_projector :
    let p := projectiveLaurentPairProjector k j
    let q := (singleTransferSheafMinus k).map
      ((transferPairCokernelFunctor k).map (laurentPairProjector k J))
    p ≫ (projectiveLaurentPairComparison k j).hom =
      (projectiveLaurentPairComparison k j).hom ≫ q := by
  intro p q
  apply ObjectProperty.hom_ext
  let d := (projectiveLaurentPairComparison k j).hom.hom
  let e := (projectivePairTermwiseModelIso k F J).hom
  let u := (laurentCochainComparison k J).hom
  let ε := laurentCochainAugmentation k J
  let α := ((Functor.whiskerRight (laurentTensorProjector k) a).mapHomologicalComplex (.up ℤ)).app
    ((projectivePairCochain k).obj J)
  let β := (CochainComplex.singleFunctor NST 0).map
    ((transferPairCokernelFunctor k).map (laurentPairProjector k J))
  have he : p.hom ≫ e = e ≫ (Q).map α :=
    projectivePairTermwiseModelIso_coefficient k (laurentTensorProjector k) J
  have hα : α ≫ (u ≫ ε) = (u ≫ ε) ≫ β :=
    (laurentCochainComparison_projector_augmented k J).trans (Category.assoc _ _ _).symm
  have hq : q.hom = (Q).map β := rfl
  have hd : d = e ≫ (Q).map (u ≫ ε) := projectiveLaurentPairComparison_hom_hom k j
  change p.hom ≫ d = d ≫ q.hom
  rw [hq, hd]
  exact CochainComplex.SplitFactorization.comp_map_of_commSq (Q)
    α β (u ≫ ε) (u ≫ ε) p.hom e e hα he

end Unreduced

local notation "U₁" => projectiveTorusTensorToDerivedMinus k

variable [IsOpenImmersion j.left] [PerfectField k]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "M" => effectiveReflection k
local notation "L" => effectiveReducedTorusTensorFunctor k

/-- Compare the original reduced coefficient model with the reduced torus
tensor of the actual relative motive. Both comparisons use their original maps. -/
def projectiveReducedLaurentPairComparison :
    (projectiveEffectiveTorus k).obj K ≅ (L).obj (effectivePairMotive k j) :=
  (projectiveEffectiveTorusNatIso k).app K ≪≫
    ((M) ⋙ (L)).mapIso (asIso (projectivePairDerivedAugmentation k J))

set_option maxHeartbeats 650000 in
-- Evaluate the composition of the original natural iso and the degree-zero augmentation.
/-- The reduced comparison is the component of the original torus isomorphism,
followed by the actual reflected augmentation. -/
theorem projectiveReducedLaurentPairComparison_hom :
    let e := projectiveEffectiveTorusNatIso k
    let C := (M) ⋙ (L)
    let t := projectivePairDerivedAugmentation k J
    (projectiveReducedLaurentPairComparison k j).hom =
      e.hom.app K ≫ C.map t := by
  intro e C t
  unfold projectiveReducedLaurentPairComparison
  rfl

variable [IsOpenImmersion (torusCylinder.map j).left]

private def retractOfSplitQuotient {C : Type*} [Category* C] {A B X Y : C}
    (e : A ≅ Y) (b : B ≅ X) (q : A ⟶ B) (s : B ⟶ A)
    (h : s ≫ q = 𝟙 B) : Retract X Y :=
  ⟨b.inv ≫ s ≫ e.hom, e.inv ≫ q ≫ b.hom, by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% h, Iso.inv_hom_id]⟩

set_option maxHeartbeats 700000 in
-- Use the two actual comparison isomorphisms on the split coefficient quotient.
/-- The relative Laurent pair contains the actual reduced torus tensor
of the original relative motive as a split summand. -/
@[no_expose]
def effectiveRelativeLaurentRetract :
    Retract ((L).obj (effectivePairMotive k j)) (effectivePairMotive k (torusCylinder.map j)) := by
  let e := (M).mapIso (projectiveLaurentPairComparison k j)
  let b := projectiveReducedLaurentPairComparison k j
  let q := (M).map ((projectiveReducedTorusTensorQuotient k).app K)
  let s := (M).map ((projectiveReducedTorusTensorSection k).app K)
  have h : s ≫ q = 𝟙 _ := by
    rw [← (M).map_comp, projectiveReducedTorusTensorSection_quotient, (M).map_id]
  exact retractOfSplitQuotient e b q s h

set_option maxHeartbeats 600000 in
-- Evaluate the transported quotient on the original retract.
/-- The retraction is the original coefficient quotient transported by the two comparisons. -/
theorem effectiveRelativeLaurentRetract_r :
    let e := (M).mapIso (projectiveLaurentPairComparison k j)
    let b := projectiveReducedLaurentPairComparison k j
    let q := (M).map ((projectiveReducedTorusTensorQuotient k).app K)
    (effectiveRelativeLaurentRetract k j).r = e.inv ≫ q ≫ b.hom := by
  intro e b q
  unfold effectiveRelativeLaurentRetract retractOfSplitQuotient
  rfl

set_option maxHeartbeats 750000 in
-- Apply effective reflection to the actual coefficient splitting and comparison.
/-- The complementary projector is the identity minus the actual unit projector
on the original relative Laurent motive. -/
theorem effectiveRelativeLaurentRetract_projector :
    (effectiveRelativeLaurentRetract k j).r ≫ (effectiveRelativeLaurentRetract k j).i =
      𝟙 _ - (effectivePairMotiveFunctor k).map (laurentPairProjector k J) := by
  let e := (M).mapIso (projectiveLaurentPairComparison k j)
  let b := projectiveReducedLaurentPairComparison k j
  let q := (M).map ((projectiveReducedTorusTensorQuotient k).app K)
  let s := (M).map ((projectiveReducedTorusTensorSection k).app K)
  let P := (effectivePairMotiveFunctor k).map (laurentPairProjector k J)
  have hp : (M).map (projectiveLaurentPairProjector k j) ≫ e.hom = e.hom ≫ P := by
    change (M).map (projectiveLaurentPairProjector k j) ≫
        (M).map (projectiveLaurentPairComparison k j).hom =
      (M).map (projectiveLaurentPairComparison k j).hom ≫
        (M).map ((singleTransferSheafMinus k).map
          ((transferPairCokernelFunctor k).map (laurentPairProjector k J)))
    exact map_comp_eq (M) (projectiveLaurentPairComparison_projector k j)
  change (e.inv ≫ q ≫ b.hom) ≫ (b.inv ≫ s ≫ e.hom) = 𝟙 _ - P
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc q, ← (M).map_comp, projectiveReducedTorusTensorQuotient_section]
  change e.inv ≫ (M).map (𝟙 ((U₁).obj K) - projectiveLaurentPairProjector k j) ≫ e.hom =
    𝟙 _ - P
  rw [(M).map_sub, (M).map_id, Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
    hp, Iso.inv_hom_id, Iso.inv_hom_id_assoc]
  rfl

end AlgebraicGeometry.MotivicHomotopy
