/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SerreSections
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic

/-!
# Native Serre sections with values on the entire closed boundary

The quotient is the actual structure-sheaf map of the given closed immersion. Its
surjectivity and the coherence of its kernel are derived, rather than supplied as input.
All sections are on the unchanged proper scheme. The boundary can be nonreduced.

This is the native closed-boundary section-lifting step of
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Data/Serre.lean`, blob
`a291270368be1902e271bc9cf1b5a91780200938`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
It does not yet construct a boundary frame, a finite-flat zero divisor, or a correction.
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

/-- The whole closed boundary receives every prescribed value of the actual twisted
structure-sheaf quotient for all sufficiently high powers of the ample bundle. -/
theorem exists_eventually_surjective_boundary_sections :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((twistFunctor L (n : ℤ)).map
          (ClosedImmersionCoherentImage.unitToPushforwardUnit i))).hom := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  letI : ((Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)).IsCoherent :=
    ClosedImmersionCoherentImage.isCoherent_pushforward_unit i
  letI : Epi (ClosedImmersionCoherentImage.unitToPushforwardUnit i) :=
    ClosedImmersionCoherentImage.epi_unitToPushforwardUnit i
  exact exists_eventually_surjective_twisted_quotient f L hL
    (ClosedImmersionCoherentImage.unitToPushforwardUnit i)

end AlgebraicGeometry.Scheme.RelativeCurvePencil
