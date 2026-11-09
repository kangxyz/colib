/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Coproducts.PartialIdentity
public import Colib.AlgebraicGeometry.Correspondences.Coproducts.Zero
public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward
public import Colib.AlgebraicGeometry.Sites.Smooth.Coproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Actual disjoint unions as correspondence biproducts

The literal smooth disjoint union, with its genuine graph inclusions, is a
binary coproduct in the existing native correspondence category. The two
clopen diagonal portions yield actual projections and all five biproduct
matrix identities. Native category theory then supplies finite biproducts.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Coproducts/Binary.lean`,
blob `993ffbf915b22adc8cec07f62ccbc3e35049608e`. The new partial-identity
lemma uses native generic-point cycles rather than the original Finsupp basis.
No topology, sheaf condition, or formal coproduct model is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- The actual disjoint-union object in the correspondence category. -/
def coproduct (X Y : Cor k) : Cor k :=
  ⟨SmoothSite.coproduct X.toSmoothSite Y.toSmoothSite⟩

/-- The first coproduct inclusion is its genuine componentwise graph cycle. -/
def coproductInl (X Y : Cor k) : X ⟶ coproduct k X Y :=
  (graphFunctor k).map (SmoothSite.coproductInl X.toSmoothSite Y.toSmoothSite)

/-- The second coproduct inclusion is its genuine componentwise graph cycle. -/
def coproductInr (X Y : Cor k) : Y ⟶ coproduct k X Y :=
  (graphFunctor k).map (SmoothSite.coproductInr X.toSmoothSite Y.toSmoothSite)

/-- The two clopen portions partition the genuine full diagonal component by component. -/
theorem partialIdentity_inl_add_inr (X Y : SmoothSite (Spec (.of k))) :
    partialIdentity k (SmoothSite.coproductInl X Y) +
      partialIdentity k (SmoothSite.coproductInr X Y) =
        𝟙 (Cor.mk (SmoothSite.coproduct X Y)) := by
  classical
  let := (finite_genericPoints k (Cor.mk (SmoothSite.coproduct X Y))).fintype
  rw [identity_eq_sum_diagonalPrime]
  unfold partialIdentity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  obtain h | h := SmoothSite.irreducibleComponent_subset_coproduct_range X Y s.property
  · have hn := SmoothSite.irreducibleComponent_not_subset_both_coproduct_ranges X Y s.property
    have h' : ¬ closure {s.val} ⊆ Set.range (SmoothSite.coproductInr X Y).left :=
      fun h' => hn ⟨h, h'⟩
    simp only [ite_eq_left h, ite_eq_right h', add_zero]
  · have hn := SmoothSite.irreducibleComponent_not_subset_both_coproduct_ranges X Y s.property
    have h' : ¬ closure {s.val} ⊆ Set.range (SmoothSite.coproductInl X Y).left :=
      fun h' => hn ⟨h', h⟩
    simp only [ite_eq_left h, ite_eq_right h', zero_add]

/-- Genuine inverse-clopen-graph cycles satisfy the five biproduct matrix identities. -/
theorem exists_coproduct_projections (X Y : Cor k) :
    ∃ (p : coproduct k X Y ⟶ X) (q : coproduct k X Y ⟶ Y),
      coproductInl k X Y ≫ p = 𝟙 X ∧
      coproductInl k X Y ≫ q = 0 ∧
      coproductInr k X Y ≫ p = 0 ∧
      coproductInr k X Y ≫ q = 𝟙 Y ∧
      p ≫ coproductInl k X Y + q ≫ coproductInr k X Y = 𝟙 (coproduct k X Y) := by
  obtain ⟨p₀, hp⟩ := exists_partialIdentity_factorization k
    (SmoothSite.coproductInl X.toSmoothSite Y.toSmoothSite)
  obtain ⟨q₀, hq⟩ := exists_partialIdentity_factorization k
    (SmoothSite.coproductInr X.toSmoothSite Y.toSmoothSite)
  let p : coproduct k X Y ⟶ X := p₀
  let q : coproduct k X Y ⟶ Y := q₀
  let i := coproductInl k X Y
  let j := coproductInr k X Y
  change p ≫ i = partialIdentity k
    (SmoothSite.coproductInl X.toSmoothSite Y.toSmoothSite) at hp
  change q ≫ j = partialIdentity k
    (SmoothSite.coproductInr X.toSmoothSite Y.toSmoothSite) at hq
  have hi : Mono i := graph_map_mono_of_isClosedImmersion k _
  have hj : Mono j := graph_map_mono_of_isClosedImmersion k _
  have htotal : p ≫ i + q ≫ j = 𝟙 (coproduct k X Y) := by
    rw [hp, hq]
    exact partialIdentity_inl_add_inr k X.toSmoothSite Y.toSmoothSite
  have hij : i ≫ q = 0 := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hq, zero_comp]
    exact graph_comp_partialIdentity_eq_zero k _ _
      (isCompl_range_inl_inr X.toSmoothSite.left Y.toSmoothSite.left).disjoint
  have hji : j ≫ p = 0 := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hp, zero_comp]
    exact graph_comp_partialIdentity_eq_zero k _ _
      (isCompl_range_inl_inr X.toSmoothSite.left Y.toSmoothSite.left).disjoint.symm
  have hii : i ≫ p = 𝟙 X := by
    apply (cancel_mono i).mp
    have hh := congrArg (fun a => i ≫ a) htotal
    simpa only [Preadditive.comp_add, ← Category.assoc, hij, zero_comp,
      add_zero, Category.comp_id, Category.id_comp] using hh
  have hjj : j ≫ q = 𝟙 Y := by
    apply (cancel_mono j).mp
    have hh := congrArg (fun a => j ≫ a) htotal
    simpa only [Preadditive.comp_add, ← Category.assoc, hji, zero_comp,
      zero_add, Category.comp_id, Category.id_comp] using hh
  exact ⟨p, q, hii, hij, hji, hjj, htotal⟩

/-- The actual graph inclusions exhibit disjoint union as a categorical coproduct. -/
def coproductIsColimit (X Y : Cor k) :
    IsColimit (BinaryCofan.mk (coproductInl k X Y) (coproductInr k X Y)) := by
  let p := (exists_coproduct_projections k X Y).choose
  let q := (exists_coproduct_projections k X Y).choose_spec.choose
  obtain ⟨hp, hq, hp', hq', htotal⟩ :=
    (exists_coproduct_projections k X Y).choose_spec.choose_spec
  change coproductInl k X Y ≫ p = _ at hp
  change coproductInl k X Y ≫ q = _ at hq
  change coproductInr k X Y ≫ p = _ at hp'
  change coproductInr k X Y ≫ q = _ at hq'
  refine BinaryCofan.IsColimit.mk _ (fun f g => p ≫ f + q ≫ g) ?_ ?_ ?_
  · intro T f g
    change coproductInl k X Y ≫ (p ≫ f + q ≫ g) = f
    simp only [Preadditive.comp_add, ← Category.assoc, hp, hq, Category.id_comp,
      zero_comp, add_zero]
  · intro T f g
    change coproductInr k X Y ≫ (p ≫ f + q ≫ g) = g
    simp only [Preadditive.comp_add, ← Category.assoc, hp', hq', Category.id_comp,
      zero_comp, zero_add]
  · intro T f g m hm₁ hm₂
    change coproductInl k X Y ≫ m = f at hm₁
    change coproductInr k X Y ≫ m = g at hm₂
    calc
      m = (p ≫ coproductInl k X Y + q ≫ coproductInr k X Y) ≫ m := by
        rw [htotal, Category.id_comp]
      _ = p ≫ f + q ≫ g := by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, hm₁, hm₂]

instance (X Y : Cor k) : HasBinaryCoproduct X Y :=
  ⟨⟨_, coproductIsColimit k X Y⟩⟩

instance : HasBinaryCoproducts (Cor k) := hasBinaryCoproducts_of_hasColimit_pair _

instance : HasBinaryBiproducts (Cor k) := HasBinaryBiproducts.of_hasBinaryCoproducts

/-- Restriction along the actual graph inclusions is a bijection on correspondence groups. -/
theorem coproduct_restriction_bijective (X Y T : Cor k) :
    Function.Bijective (fun α : coproduct k X Y ⟶ T =>
      (coproductInl k X Y ≫ α, coproductInr k X Y ≫ α)) := by
  constructor
  · intro α β h
    apply (coproductIsColimit k X Y).hom_ext
    intro j
    cases j with
    | mk j => cases j
              · exact congrArg Prod.fst h
              · exact congrArg Prod.snd h
  · rintro ⟨α, β⟩
    refine ⟨(coproductIsColimit k X Y).desc (BinaryCofan.mk α β), ?_⟩
    ext
    · exact (coproductIsColimit k X Y).fac (BinaryCofan.mk α β) ⟨WalkingPair.left⟩
    · exact (coproductIsColimit k X Y).fac (BinaryCofan.mk α β) ⟨WalkingPair.right⟩

instance : HasFiniteCoproducts (Cor k) := hasFiniteCoproducts_of_has_binary_and_initial

instance : HasFiniteBiproducts (Cor k) := HasFiniteBiproducts.of_hasFiniteCoproducts

end AlgebraicGeometry.Cor
