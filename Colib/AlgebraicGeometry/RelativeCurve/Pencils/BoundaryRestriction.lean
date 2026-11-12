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
open Stacks.AffineClosedUnion (twistUnitIso twistPushforwardIso twistedUnit_eq_unit
  unitToPushforwardStructureSheaf)

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {X S Z : Scheme.{u}} (f : X ⟶ S)
  [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
  (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
  (i : Z ⟶ X) [IsClosedImmersion i]

/-- Surjectivity of the evaluated twisted quotient gives surjectivity of actual
pullback on global sections, via the native projection formula and adjunction. -/
theorem surjective_pullbackGlobalSections_of_twisted_quotient (A : X.Modules)
    (h : Function.Surjective
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((Stacks.AffineClosedUnion.twistFunctor X A).map
          (unitToPushforwardStructureSheaf i))).hom) :
    Function.Surjective (pullbackGlobalSections i A) := by
  let ev := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let α := (twistUnitIso A).inv
  let π := (Stacks.AffineClosedUnion.twistFunctor X A).map (unitToPushforwardStructureSheaf i)
  let β := (twistPushforwardIso i A).hom
  let η := (Modules.pullbackPushforwardAdjunction i).unit.app A
  have hπ : Epi (ev.map π) := (ModuleCat.epi_iff_surjective _).2 h
  let eα := ev.mapIso (twistUnitIso A)
  let eβ := ev.mapIso (twistPushforwardIso i A)
  have hα : Epi (ev.map α) := @IsIso.epi_of_iso _ _ _ _ eα.inv eα.isIso_inv
  have hβ : Epi (ev.map β) := @IsIso.epi_of_iso _ _ _ _ eβ.hom eβ.isIso_hom
  have hmap : ev.map η = ev.map α ≫ ev.map π ≫ ev.map β :=
    (congrArg (fun m => ev.map m) (twistedUnit_eq_unit i A).symm).trans
      ((ev.map_comp α (π ≫ β)).trans
        (congrArg (fun m => ev.map α ≫ m) (ev.map_comp π β)))
  have hη : Epi (ev.map η) := hmap.symm ▸ epi_comp' hα (epi_comp' hπ hβ)
  intro a
  obtain ⟨s, hs⟩ := (ModuleCat.epi_iff_surjective (ev.map η)).1 hη a
  exact ⟨s, (SectionsEqualizer.pullbackGlobalSections_unit i A s).trans hs⟩

include f hL

/-- Every sufficiently high ample power restricts surjectively to the entire
scheme-theoretic boundary, through the actual native pullback map on sections. -/
theorem exists_eventually_surjective_boundary_restriction :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      (pullbackGlobalSections i (tensorPowModule X L (n : ℤ))) := by
  obtain ⟨N, hN⟩ := exists_eventually_surjective_boundary_sections f L hL i
  exact ⟨N, fun n hn => surjective_pullbackGlobalSections_of_twisted_quotient i _ (hN n hn)⟩

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
        e.hom.app ⊤ (pullbackGlobalSections i (tensorPowModule X L (n : ℤ)) s) =
          (1 : Γ(Z, ⊤)) := by
  obtain ⟨N, hN⟩ := exists_eventually_surjective_boundary_restriction f L hL i
  refine ⟨N, fun n hn e => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn (Modules.Hom.app e.inv ⊤ (1 : Γ(Z, ⊤)))
  let U : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  have h := congrArg (fun m : U ⟶ U =>
    Modules.Hom.app (X := Z) m ⊤ (1 : Γ(Z, ⊤))) e.inv_hom_id
  exact ⟨s, (congrArg (fun a => e.hom.app ⊤ a) hs).trans h⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
