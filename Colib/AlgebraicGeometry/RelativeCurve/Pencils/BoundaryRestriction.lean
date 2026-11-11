/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundarySerre
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.TwistedUnit
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections

/-!
# Actual whole-boundary restriction from native Serre lifting

The earlier Serre theorem lifts sections of the actual twisted structure-sheaf quotient.
The pinned projection formula identifies that quotient with the direct image of the
pulled-back ample power. Its coherence theorem identifies the conjugated quotient map
with the unit of pullback and pushforward. Thus the resulting section-surjectivity is
for the literal `pullbackGlobalSections` map, not an unspecified isomorphic map.

This is the ample-power part of the original boundary section producer in
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Data/Serre.lean`, blob
`a291270368be1902e271bc9cf1b5a91780200938`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
The fixed diagonal-line tensor factor needed by the normalized numerator is not yet
included in this statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Ample Stacks.AlgebraicGeometry.RelativeSerreVanishing

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {X S Z : Scheme.{u}} (f : X ⟶ S)
  [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
  (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- Every sufficiently high ample power restricts surjectively to the entire
scheme-theoretic boundary, through the actual native pullback map on sections. -/
theorem exists_eventually_surjective_boundary_restriction :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      (pullbackGlobalSections i (tensorPowModule X L (n : ℤ))) := by
  obtain ⟨N, hN⟩ := exists_eventually_surjective_boundary_sections f L hL i
  refine ⟨N, fun n hn => ?_⟩
  let A : X.Modules := tensorPowModule X L (n : ℤ)
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  have hsurj := hN n hn
  change Function.Surjective
    (ev.map ((Stacks.AffineClosedUnion.twistFunctor X A).map
      (Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf i))).hom at hsurj
  have : Epi (ev.map ((Stacks.AffineClosedUnion.twistFunctor X A).map
      (Stacks.AffineClosedUnion.unitToPushforwardStructureSheaf i))) :=
    (ModuleCat.epi_iff_surjective _).2 hsurj
  have : Epi (ev.map (Stacks.AffineClosedUnion.twistedUnit i A)) := by
    rw [Stacks.AffineClosedUnion.twistedUnit, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hu := (ModuleCat.epi_iff_surjective
    (ev.map (Stacks.AffineClosedUnion.twistedUnit i A))).1 inferInstance
  rw [Stacks.AffineClosedUnion.twistedUnit_eq_unit] at hu
  intro a
  obtain ⟨s, hs⟩ := hu a
  exact ⟨s, (SectionsEqualizer.pullbackGlobalSections_unit i A s).trans hs⟩

/-- The Serre bound supplies an actual section with each chosen whole-boundary value. -/
theorem exists_eventually_prescribed_boundary_section :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ a : Γ((Modules.pullback i).obj (tensorPowModule X L (n : ℤ)), ⊤),
      ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
        pullbackGlobalSections i (tensorPowModule X L (n : ℤ)) s = a :=
  exists_eventually_surjective_boundary_restriction f L hL i

/-- A supplied whole-boundary trivialization determines a value, and Serre constructs
a genuine global section with exactly that value. Neither the section nor a lifting
property is an input. This does not construct the boundary trivialization itself. -/
theorem exists_eventually_boundary_frame_section :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ e : (Modules.pullback i).obj (tensorPowModule X L (n : ℤ)) ≅
        SheafOfModules.unit Z.ringCatSheaf,
      ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
        e.hom.app ⊤ (pullbackGlobalSections i (tensorPowModule X L (n : ℤ)) s) = 1 := by
  obtain ⟨N, hN⟩ := exists_eventually_surjective_boundary_restriction f L hL i
  refine ⟨N, fun n hn e => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn (e.inv.app ⊤ 1)
  refine ⟨s, ?_⟩
  rw [hs]
  have h := congrArg (fun m => m.app ⊤ (1 : Γ(Z, ⊤))) e.inv_hom_id
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    CategoryTheory.comp_apply, CategoryTheory.id_apply] using h

end AlgebraicGeometry.Scheme.RelativeCurvePencil
