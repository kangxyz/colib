/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryRestriction
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced

/-!
# Whole-boundary Serre restriction with a fixed invertible factor

The numerator in the original normalized divisor pair is a large ample twist of the
dual graph line. It is not an ample power alone. Tensor the actual closed-boundary
quotient by this fixed factor before applying coherent Serre vanishing. Naturality
of the native tensor associator then identifies the map with the actual restriction
of the fixed factor tensored with the ample power.

This implements the fixed-factor step of the original
`RelativeCurve/Pencils/Data/Serre.lean` (blob
`a291270368be1902e271bc9cf1b5a91780200938`) at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Ample Stacks.AlgebraicGeometry.RelativeSerreVanishing

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

/-- The fixed native associator, as an isomorphism of tensoring functors. -/
def fixedFactorTwistIso (X : Scheme.{u}) (F A : X.Modules) :
    Stacks.AffineClosedUnion.twistFunctor X F ⋙
        Stacks.AffineClosedUnion.twistFunctor X A ≅
      Stacks.AffineClosedUnion.twistFunctor X
        ((Stacks.AffineClosedUnion.twistFunctor X A).obj F) := by
  letI := Stacks.SheafOfModules.sheafTensorMonoidal X.presheaf X.ringCatSheaf.2
  refine NatIso.ofComponents
    (fun M => Stacks.SheafOfModules.Invertible.tensorProductAssociator
      X.presheaf X.ringCatSheaf.2 M F A) ?_
  intro M N g
  exact MonoidalCategory.associator_naturality_left g F A

variable {X S Z : Scheme.{u}} (f : X ⟶ S)
  [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
  (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- The actual restriction of `F tensor L^n` to the entire closed boundary is
surjective for every sufficiently large `n`. The fixed invertible module `F`
need not be ample. Coherence, the quotient epimorphism and vanishing are derived. -/
theorem exists_eventually_surjective_fixedFactor_boundary_restriction
    (F : X.Modules) [IsInvertibleModule X F] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      (pullbackGlobalSections i ((twistFunctor L (n : ℤ)).obj F)) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let U := SheafOfModules.unit X.ringCatSheaf
  let Q := (Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let π : U ⟶ Q := ClosedImmersionCoherentImage.unitToPushforwardUnit i
  let T := Stacks.AffineClosedUnion.twistFunctor X F
  letI : U.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  letI : Q.IsCoherent := ClosedImmersionCoherentImage.isCoherent_pushforward_unit i
  letI : Epi π := ClosedImmersionCoherentImage.epi_unitToPushforwardUnit i
  letI : T.IsEquivalence :=
    Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence
      X.presheaf X.ringCatSheaf.2 F
  letI : (T.obj U).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X U F
  letI : (T.obj Q).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X Q F
  obtain ⟨N, hN⟩ := exists_eventually_surjective_twisted_quotient f L hL (T.map π)
  refine ⟨N, fun n hn => ?_⟩
  let A : X.Modules := tensorPowModule X L (n : ℤ)
  let B : X.Modules := (Stacks.AffineClosedUnion.twistFunctor X A).obj F
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let e := fixedFactorTwistIso X F A
  have hsurj := hN n hn
  letI : Epi (ev.map ((T ⋙ Stacks.AffineClosedUnion.twistFunctor X A).map π)) :=
    (ModuleCat.epi_iff_surjective _).2 hsurj
  have hconj : (Stacks.AffineClosedUnion.twistFunctor X B).map π =
      (e.app U).inv ≫
        (T ⋙ Stacks.AffineClosedUnion.twistFunctor X A).map π ≫ (e.app Q).hom := by
    rw [e.hom.naturality π, Iso.inv_hom_id_assoc]
  letI : Epi (ev.map ((Stacks.AffineClosedUnion.twistFunctor X B).map π)) := by
    rw [hconj, Functor.map_comp, Functor.map_comp]
    infer_instance
  letI : Epi (ev.map (Stacks.AffineClosedUnion.twistedUnit i B)) := by
    rw [Stacks.AffineClosedUnion.twistedUnit, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hu := (ModuleCat.epi_iff_surjective
    (ev.map (Stacks.AffineClosedUnion.twistedUnit i B))).1 inferInstance
  rw [Stacks.AffineClosedUnion.twistedUnit_eq_unit] at hu
  intro a
  obtain ⟨s, hs⟩ := hu a
  exact ⟨s, (SectionsEqualizer.pullbackGlobalSections_unit i B s).trans hs⟩

/-- One common bound produces an actual numerator with its fixed factor and an
actual denominator, with independently prescribed values on the full boundary. -/
theorem exists_eventually_fixedFactor_boundary_pair
    (F : X.Modules) [IsInvertibleModule X F] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ a : Γ((Modules.pullback i).obj ((twistFunctor L (n : ℤ)).obj F), ⊤),
      ∀ b : Γ((Modules.pullback i).obj (tensorPowModule X L (n : ℤ)), ⊤),
      ∃ s : Γ((twistFunctor L (n : ℤ)).obj F, ⊤),
      ∃ t : Γ(tensorPowModule X L (n : ℤ), ⊤),
        pullbackGlobalSections i _ s = a ∧ pullbackGlobalSections i _ t = b := by
  obtain ⟨N₁, h₁⟩ :=
    exists_eventually_surjective_fixedFactor_boundary_restriction f L hL i F
  obtain ⟨N₂, h₂⟩ := exists_eventually_surjective_boundary_restriction f L hL i
  refine ⟨max N₁ N₂, fun n hn a b => ?_⟩
  obtain ⟨s, hs⟩ := h₁ n ((le_max_left _ _).trans hn) a
  obtain ⟨t, ht⟩ := h₂ n ((le_max_right _ _).trans hn) b
  exact ⟨s, t, hs, ht⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
