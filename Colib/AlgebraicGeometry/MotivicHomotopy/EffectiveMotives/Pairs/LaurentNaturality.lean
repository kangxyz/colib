/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.LaurentRetract
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap

/-! # Naturality of the original Laurent comparison and its reduced projection -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "NST" => LargeSheaves k
local notation "F" => parameterTensorFunctor G
local notation "a" => nisnevichSheafify k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance laurentNaturalityAbelian : Abelian NST := SheafWithTransfers.abelian k

private theorem map_comp_eq {C D : Type*} [Category* C] [Category* D] (M₀ : C ⥤ D)
    {A B B' D₀ : C} {f : A ⟶ B} {g : B ⟶ D₀} {f' : A ⟶ B'} {g' : B' ⟶ D₀}
    (h : f ≫ g = f' ≫ g') : M₀.map f ≫ M₀.map g = M₀.map f' ≫ M₀.map g' :=
  (M₀.map_comp _ _).symm.trans ((M₀.congr_map h).trans (M₀.map_comp _ _))

private theorem iso_projection_naturality {C : Type*} [Category* C]
    {A A' B B' X X' Y Y' : C}
    (e : A ≅ Y) (e' : A' ≅ Y') (b : B ≅ X) (b' : B' ≅ X')
    (q : A ⟶ B) (q' : A' ⟶ B') (u : A ⟶ A') (v : B ⟶ B') (f : Y ⟶ Y') (g : X ⟶ X')
    (he : u ≫ e'.hom = e.hom ≫ f) (hq : u ≫ q' = q ≫ v)
    (hb : v ≫ b'.hom = b.hom ≫ g) :
    f ≫ (e'.inv ≫ q' ≫ b'.hom) = (e.inv ≫ q ≫ b.hom) ≫ g := by
  have h : f ≫ e'.inv = e.inv ≫ u := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, reassoc_of% hq, hb]
  simp only [Category.assoc]

private theorem comp_square {C : Type*} [Category* C]
    {A A' B B' D₀ D' : C} {f : A ⟶ A'} {g : B ⟶ B'} {h : D₀ ⟶ D'}
    {a₀ : A ⟶ B} {a₁ : A' ⟶ B'} {b₀ : B ⟶ D₀} {b₁ : B' ⟶ D'}
    (ha : f ≫ a₁ = a₀ ≫ g) (hb : g ≫ b₁ = b₀ ≫ h) :
    f ≫ (a₁ ≫ b₁) = (a₀ ≫ b₀) ≫ h := by
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

set_option maxHeartbeats 750000 in
-- Assemble the two original cochain equations before taking the derived quotient.
private theorem laurentCochainAugmentation_naturality {U X U' X' : Sm(k)}
    (j : U ⟶ X) (j' : U' ⟶ X') (φ : Arrow.mk j ⟶ Arrow.mk j') :
    let A := (F ⋙ a).mapHomologicalComplex (.up ℤ)
    let f := A.map ((projectivePairCochain k).map φ)
    let h := (CochainComplex.singleFunctor NST 0).map
      ((transferPairCokernelFunctor k).map ((laurentPair k).map φ))
    let l₀ := (laurentCochainComparison k (Arrow.mk j)).hom
    let l₁ := (laurentCochainComparison k (Arrow.mk j')).hom
    let q₀ := laurentCochainAugmentation k (Arrow.mk j)
    let q₁ := laurentCochainAugmentation k (Arrow.mk j')
    f ≫ (l₁ ≫ q₁) = (l₀ ≫ q₀) ≫ h := by
  intro A f h l₀ l₁ q₀ q₁
  let g := cochainTransferPairConeMap k ((laurentPair k).map φ)
  have hl : f ≫ l₁ = l₀ ≫ g := laurentCochainComparison_naturality k φ
  have hq : g ≫ q₁ = q₀ ≫ h := cochainTransferPairConeMap_desc k ((laurentPair k).map φ)
  exact comp_square hl hq

variable [HasDerivedCategory.{w} (LargePresheaves k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]

local notation "Q" => (DerivedCategory.Q : CochainComplex NST ℤ ⥤ DerivedCategory NST)

variable {U X : Sm(k)} (j : U ⟶ X)

local notation "J" => Arrow.mk j
set_option quotPrecheck false in
local notation "K" => (projectivePairDerived k).obj J
local notation "U₁" => projectiveTorusTensorToDerivedMinus k

section Unreduced

variable [IsOpenImmersion (torusCylinder.map j).left]

variable {U' X' : Sm(k)} (j' : U' ⟶ X')
  (φ : Arrow.mk j ⟶ Arrow.mk j')
variable [IsOpenImmersion (torusCylinder.map j').left]

set_option maxHeartbeats 850000 in
-- Paste the termwise comparison with the mapped cochain square.
/-- Laurent coefficients on the two original pair models compare by their actual graph maps. -/
theorem projectiveLaurentPairComparison_naturality :
    let u := (projectivePairDerived k).map φ
    let v := (singleTransferSheafMinus k).map
      ((transferPairCokernelFunctor k).map ((laurentPair k).map φ))
    (U₁).map u ≫ (projectiveLaurentPairComparison k j').hom =
      (projectiveLaurentPairComparison k j).hom ≫ v := by
  intro u v
  apply ObjectProperty.hom_ext
  let d₀ := (projectiveLaurentPairComparison k j).hom.hom
  let d₁ := (projectiveLaurentPairComparison k j').hom.hom
  let e₀ := (projectivePairTermwiseModelIso k F (Arrow.mk j)).hom
  let e₁ := (projectivePairTermwiseModelIso k F (Arrow.mk j')).hom
  let l₀ := (laurentCochainComparison k (Arrow.mk j)).hom
  let l₁ := (laurentCochainComparison k (Arrow.mk j')).hom
  let q₀ := laurentCochainAugmentation k (Arrow.mk j)
  let q₁ := laurentCochainAugmentation k (Arrow.mk j')
  let A := (F ⋙ a).mapHomologicalComplex (.up ℤ)
  let f := A.map ((projectivePairCochain k).map φ)
  let h := (CochainComplex.singleFunctor NST 0).map
    ((transferPairCokernelFunctor k).map ((laurentPair k).map φ))
  have he : ((U₁).map u).hom ≫ e₁ = e₀ ≫ (Q).map f :=
    projectivePairTermwiseModelIso_naturality k F φ
  have hn : f ≫ (l₁ ≫ q₁) = (l₀ ≫ q₀) ≫ h := laurentCochainAugmentation_naturality k j j' φ
  have hd₀ : d₀ = e₀ ≫ (Q).map (l₀ ≫ q₀) := projectiveLaurentPairComparison_hom_hom k j
  have hd₁ : d₁ = e₁ ≫ (Q).map (l₁ ≫ q₁) := projectiveLaurentPairComparison_hom_hom k j'
  have hv : v.hom = (Q).map h := rfl
  change ((U₁).map u).hom ≫ d₁ = d₀ ≫ v.hom
  rw [hd₀, hd₁, hv]
  exact CochainComplex.SplitFactorization.comp_map_of_commSq (Q)
    f h (l₀ ≫ q₀) (l₁ ≫ q₁) ((U₁).map u).hom e₀ e₁ hn he

end Unreduced

variable [PerfectField k]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "M" => effectiveReflection k
local notation "L" => effectiveReducedTorusTensorFunctor k

section ReflectedComparison

variable {U' X' : Sm(k)} (j' : U' ⟶ X')
  [IsOpenImmersion (torusCylinder.map j).left] [IsOpenImmersion (torusCylinder.map j').left]
  (φ : Arrow.mk j ⟶ Arrow.mk j')

set_option maxHeartbeats 600000 in
-- Apply reflection to the commuting square of unreduced derived comparisons.
private theorem reflectedLaurentComparison_naturality :
    let u := (projectivePairDerived k).map φ
    let v := (effectivePairMotiveFunctor k).map ((laurentPair k).map φ)
    let e₀ := (M).mapIso (projectiveLaurentPairComparison k j)
    let e₁ := (M).mapIso (projectiveLaurentPairComparison k j')
    (M).map ((U₁).map u) ≫ e₁.hom = e₀.hom ≫ v := by
  intro u v e₀ e₁
  let d₀ := (projectiveLaurentPairComparison k j).hom
  let d₁ := (projectiveLaurentPairComparison k j').hom
  let g := (singleTransferSheafMinus k).map
    ((transferPairCokernelFunctor k).map ((laurentPair k).map φ))
  have h : (U₁).map u ≫ d₁ = d₀ ≫ g := projectiveLaurentPairComparison_naturality k j j' φ
  change (M).map ((U₁).map u) ≫ (M).map d₁ = (M).map d₀ ≫ (M).map g
  exact map_comp_eq (M) h

end ReflectedComparison

section ReflectedQuotient

variable {U' X' : Sm(k)} (j' : U' ⟶ X') (φ : Arrow.mk j ⟶ Arrow.mk j')

set_option maxHeartbeats 600000 in
-- Apply reflection to the naturality of the original projective Laurent quotient.
private theorem reflectedLaurentQuotient_naturality :
    let u := (projectivePairDerived k).map φ
    let q₀ := (M).map ((projectiveReducedTorusTensorQuotient k).app K)
    let q₁ := (M).map ((projectiveReducedTorusTensorQuotient k).app
      ((projectivePairDerived k).obj (Arrow.mk j')))
    (M).map ((U₁).map u) ≫ q₁ = q₀ ≫ (projectiveEffectiveTorus k).map u := by
  intro u q₀ q₁
  let q := projectiveReducedTorusTensorQuotient k
  let q_src := q.app K
  let q_tgt := q.app ((projectivePairDerived k).obj (Arrow.mk j'))
  let g := (projectiveReducedTorusTensorToDerivedMinus k).map u
  have h : (U₁).map u ≫ q_tgt = q_src ≫ g := q.naturality u
  change (M).map ((U₁).map u) ≫ (M).map q_tgt = (M).map q_src ≫ (M).map g
  exact map_comp_eq (M) h

end ReflectedQuotient

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

section ReducedNaturality

variable {U' X' : Sm(k)} (j' : U' ⟶ X')
  (φ : Arrow.mk j ⟶ Arrow.mk j')

set_option maxHeartbeats 850000 in
-- Paste the natural comparison with the mapped augmentation.
private theorem projectiveReducedLaurentPairComparison_naturality_aux :
    let u := (projectivePairDerived k).map φ
    let e := projectiveEffectiveTorusNatIso k
    let b₀ := e.hom.app K
    let b₁ := e.hom.app ((projectivePairDerived k).obj (Arrow.mk j'))
    let t₀ := projectivePairDerivedAugmentation k (Arrow.mk j)
    let t₁ := projectivePairDerivedAugmentation k (Arrow.mk j')
    let _f := (derivedNisnevichSheafification k).map u
    let g := (singleTransferSheafMinus k).map ((transferPairCokernelFunctor k).map φ)
    let C := (M) ⋙ (L)
    (projectiveEffectiveTorus k).map u ≫ (b₁ ≫ C.map t₁) =
      (b₀ ≫ C.map t₀) ≫ C.map g := by
  intro u e b₀ b₁ t₀ t₁ f g C
  have he : (projectiveEffectiveTorus k).map u ≫ b₁ = b₀ ≫ C.map f := e.hom.naturality u
  have h : f ≫ t₁ = t₀ ≫ g := projectivePairDerivedAugmentation_naturality k φ
  exact CochainComplex.SplitFactorization.comp_map_of_commSq C f g t₀ t₁
    ((projectiveEffectiveTorus k).map u) b₀ b₁ h he

variable [IsOpenImmersion j.left] [IsOpenImmersion j'.left]

set_option maxHeartbeats 800000 in
-- Convert the typed comparison to the literal projective and effective maps.
/-- The reduced Laurent comparison uses the actual natural comparison from the torus adjunction. -/
theorem projectiveReducedLaurentPairComparison_naturality :
    let u := (projectivePairDerived k).map φ
    let v := (effectivePairMotiveFunctor k).map φ
    (projectiveEffectiveTorus k).map u ≫ (projectiveReducedLaurentPairComparison k j').hom =
      (projectiveReducedLaurentPairComparison k j).hom ≫ (L).map v := by
  intro u v
  rw [projectiveReducedLaurentPairComparison_hom k j,
    projectiveReducedLaurentPairComparison_hom k j']
  exact projectiveReducedLaurentPairComparison_naturality_aux k j j' φ

end ReducedNaturality

variable [IsOpenImmersion j.left] [IsOpenImmersion (torusCylinder.map j).left]

section EffectiveNaturality

variable {U' X' : Sm(k)} (j' : U' ⟶ X')
  [IsOpenImmersion j'.left] [IsOpenImmersion (torusCylinder.map j').left]
  (φ : Arrow.mk j ⟶ Arrow.mk j')

set_option maxHeartbeats 800000 in
-- Paste the three already identified squares in the reflected category.
private theorem effectiveRelativeLaurentRetract_naturality_aux :
    let v := (L).map ((effectivePairMotiveFunctor k).map φ)
    let f := (effectivePairMotiveFunctor k).map ((laurentPair k).map φ)
    let e₀ := (M).mapIso (projectiveLaurentPairComparison k j)
    let e₁ := (M).mapIso (projectiveLaurentPairComparison k j')
    let b₀ := projectiveReducedLaurentPairComparison k j
    let b₁ := projectiveReducedLaurentPairComparison k j'
    let q₀ := (M).map ((projectiveReducedTorusTensorQuotient k).app K)
    let q₁ := (M).map ((projectiveReducedTorusTensorQuotient k).app
      ((projectivePairDerived k).obj (Arrow.mk j')))
    f ≫ (e₁.inv ≫ q₁ ≫ b₁.hom) = (e₀.inv ≫ q₀ ≫ b₀.hom) ≫ v := by
  intro v f e₀ e₁ b₀ b₁ q₀ q₁
  let u := (projectivePairDerived k).map φ
  let h₀ := (M).map ((U₁).map u)
  let h₁ := (projectiveEffectiveTorus k).map u
  have he : h₀ ≫ e₁.hom = e₀.hom ≫ f := reflectedLaurentComparison_naturality k j j' φ
  have hq : h₀ ≫ q₁ = q₀ ≫ h₁ := reflectedLaurentQuotient_naturality k j j' φ
  have hb : h₁ ≫ b₁.hom = b₀.hom ≫ v :=
    projectiveReducedLaurentPairComparison_naturality k j j' φ
  exact iso_projection_naturality e₀ e₁ b₀ b₁ q₀ q₁ h₀ h₁ f v he hq hb

set_option maxHeartbeats 800000 in
-- Use the projection component formula at each of the two original pairs.
/-- Projection to the original reduced summand is natural for the literal maps of open pairs. -/
theorem effectiveRelativeLaurentRetract_naturality :
    let v := (effectivePairMotiveFunctor k).map φ
    let v₁ := (effectivePairMotiveFunctor k).map ((laurentPair k).map φ)
    v₁ ≫ (effectiveRelativeLaurentRetract k j').r =
      (effectiveRelativeLaurentRetract k j).r ≫ (L).map v := by
  intro v v₁
  rw [effectiveRelativeLaurentRetract_r k j, effectiveRelativeLaurentRetract_r k j']
  exact effectiveRelativeLaurentRetract_naturality_aux k j j' φ

end EffectiveNaturality

end AlgebraicGeometry.MotivicHomotopy
