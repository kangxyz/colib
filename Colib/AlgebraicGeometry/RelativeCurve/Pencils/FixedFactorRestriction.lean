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
  letI : MonoidalCategory X.Modules :=
    Stacks.SheafOfModules.sheafTensorMonoidal X.presheaf X.ringCatSheaf.2
  refine NatIso.ofComponents
    (fun M => Stacks.SheafOfModules.Invertible.tensorProductAssociator
      X.presheaf X.ringCatSheaf.2 M F A) ?_
  intro M N g
  exact MonoidalCategory.associator_naturality_left g F A

variable {X S Z : Scheme.{u}} (f : X ⟶ S)
  [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
  (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
  (i : Z ⟶ X) [IsClosedImmersion i]

include f hL

/-- The actual restriction of `F tensor L^n` to the entire closed boundary is
surjective for every sufficiently large `n`. The fixed invertible module `F`
need not be ample. Coherence, the quotient epimorphism and vanishing are derived. -/
theorem exists_eventually_surjective_fixedFactor_boundary_restriction
    (F : X.Modules) [IsInvertibleModule X F] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      (pullbackGlobalSections i ((twistFunctor L (n : ℤ)).obj F)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let U : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let Q : X.Modules := (Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let π : U ⟶ Q := ClosedImmersionCoherentImage.unitToPushforwardUnit i
  let T := Stacks.AffineClosedUnion.twistFunctor X F
  have hU : U.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hQ : Q.IsCoherent := ClosedImmersionCoherentImage.isCoherent_pushforward_unit i
  have hπ : Epi π := ClosedImmersionCoherentImage.epi_unitToPushforwardUnit i
  have hT : T.IsEquivalence :=
    Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence
      X.presheaf X.ringCatSheaf.2 F
  have hpreserves : T.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (@Functor.asEquivalence _ _ _ _ T hT).toAdjunction
  have hTπ : Epi (T.map π) := @Functor.map_epi _ _ _ _ T hpreserves _ _ π hπ
  have hTU : (T.obj U).IsCoherent :=
    @AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X U F
      hU ‹IsInvertibleModule X F›
  have hTQ : (T.obj Q).IsCoherent :=
    @AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X Q F
      hQ ‹IsInvertibleModule X F›
  obtain ⟨N, hN⟩ := @exists_eventually_surjective_twisted_quotient X S f inferInstance
    inferInstance inferInstance L inferInstance hL (T.obj U) (T.obj Q) hTU hTQ (T.map π) hTπ
  refine ⟨N, fun n hn => ?_⟩
  let A : X.Modules := tensorPowModule X L (n : ℤ)
  let P := Stacks.AffineClosedUnion.twistFunctor X A
  let B : X.Modules := P.obj F
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let e := fixedFactorTwistIso X F A
  let μ := (T ⋙ P).map π
  let α := (e.app U).inv
  let β := (e.app Q).hom
  let ρ := (Stacks.AffineClosedUnion.twistFunctor X B).map π
  have hμ : Epi (ev.map μ) := (ModuleCat.epi_iff_surjective _).2 (hN n hn)
  have hconj : ρ = α ≫ μ ≫ β :=
    ((e.app U).eq_inv_comp).2 (e.hom.naturality π).symm
  have hmap : ev.map ρ = ev.map α ≫ ev.map μ ≫ ev.map β :=
    (congrArg (fun m => ev.map m) hconj).trans
      ((ev.map_comp α (μ ≫ β)).trans (congrArg (fun m => ev.map α ≫ m) (ev.map_comp μ β)))
  let eα := ev.mapIso (e.app U)
  let eβ := ev.mapIso (e.app Q)
  have hα : Epi (ev.map α) := @IsIso.epi_of_iso _ _ _ _ eα.inv eα.isIso_inv
  have hβ : Epi (ev.map β) := @IsIso.epi_of_iso _ _ _ _ eβ.hom eβ.isIso_hom
  have hρ : Epi (ev.map ρ) := hmap.symm ▸ epi_comp' hα (epi_comp' hμ hβ)
  exact surjective_pullbackGlobalSections_of_twisted_quotient i B
    ((ModuleCat.epi_iff_surjective _).1 hρ)

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
