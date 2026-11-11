/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Hypercohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.NisnevichRepresentative

/-!
# Nisnevich representatives of integral and finite motivic cohomology

The representatives use the ordinary underlying complex of the canonical
signed transfer construction and the actual multiplication cone for finite
coefficients. The comparison with motivic cohomology is on the original
smooth representables and their restriction maps.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)

/-- The Nisnevich Eilenberg–Mac Lane representative for the integral motivic complex. -/
def motivicNisnevichRepresentative (p : ℤ) (q : ℕ) : NisnevichHomotopyCategory Sₖ :=
  nisnevichCochainRepresentative Sₖ p (motivicSheafComplex k q)

/-- The Nisnevich Eilenberg–Mac Lane representative for the finite coefficient cone. -/
def motivicFiniteNisnevichRepresentative (p : ℤ) (q n : ℕ) : NisnevichHomotopyCategory Sₖ :=
  nisnevichCochainRepresentative Sₖ p (motivicFiniteSheafComplex k q n)

variable [HasDerivedCategory.{d}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Maps from the localized smooth representable compute the existing integral motivic groups. -/
def motivicNisnevichRepresentativeHomEquiv (p : ℤ) (q : ℕ)
    (U : SmoothSite (Spec (.of k))) :
    ((pointedNisnevichYoneda Sₖ).obj U ⟶ motivicNisnevichRepresentative k p q) ≃
      motivicCohomology k p q U :=
  nisnevichCochainRepresentativeYonedaHomEquiv Sₖ p (motivicSheafComplex k q) U

/-- Maps from the localized smooth representable compute the existing cone-coefficient groups. -/
def motivicFiniteNisnevichRepresentativeHomEquiv (p : ℤ) (q n : ℕ)
    (U : SmoothSite (Spec (.of k))) :
    ((pointedNisnevichYoneda Sₖ).obj U ⟶ motivicFiniteNisnevichRepresentative k p q n) ≃
      motivicFiniteCohomology k p q n U :=
  nisnevichCochainRepresentativeYonedaHomEquiv Sₖ p (motivicFiniteSheafComplex k q n) U

/-- The integral comparison respects pullback along the original smooth-site map. -/
theorem motivicNisnevichRepresentativeHomEquiv_naturality (p : ℤ) (q : ℕ)
    {U V : SmoothSite (Spec (.of k))} (f : U ⟶ V)
    (a : (pointedNisnevichYoneda Sₖ).obj V ⟶ motivicNisnevichRepresentative k p q) :
    motivicNisnevichRepresentativeHomEquiv k p q U ((pointedNisnevichYoneda Sₖ).map f ≫ a) =
      motivicCohomologyRestriction k p q f (motivicNisnevichRepresentativeHomEquiv k p q V a) :=
  nisnevichCochainRepresentativeYonedaHomEquiv_naturality Sₖ p (motivicSheafComplex k q) f a

/-- The finite comparison respects pullback along the original smooth-site map. -/
theorem motivicFiniteNisnevichRepresentativeHomEquiv_naturality (p : ℤ) (q n : ℕ)
    {U V : SmoothSite (Spec (.of k))} (f : U ⟶ V)
    (a : (pointedNisnevichYoneda Sₖ).obj V ⟶ motivicFiniteNisnevichRepresentative k p q n) :
    motivicFiniteNisnevichRepresentativeHomEquiv k p q n U ((pointedNisnevichYoneda Sₖ).map f ≫ a) =
      motivicFiniteCohomologyRestriction k p q n f
        (motivicFiniteNisnevichRepresentativeHomEquiv k p q n V a) :=
  nisnevichCochainRepresentativeYonedaHomEquiv_naturality Sₖ p (motivicFiniteSheafComplex k q n) f a

attribute [colib_tag "COL-1015"]
  motivicNisnevichRepresentative motivicFiniteNisnevichRepresentative
  motivicNisnevichRepresentativeHomEquiv motivicFiniteNisnevichRepresentativeHomEquiv
  motivicNisnevichRepresentativeHomEquiv_naturality
  motivicFiniteNisnevichRepresentativeHomEquiv_naturality

attribute [colib_ref "Voevodsky2003ReducedPowers" "Section 2, Theorem 2.1 and equation (2.9), pp. 3–5"
  "ingredient" "The reduced derived-Hom formula used before affine-line localization"]
  motivicNisnevichRepresentativeHomEquiv motivicFiniteNisnevichRepresentativeHomEquiv

end AlgebraicGeometry.MotivicHomotopy
