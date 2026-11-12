/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Hypercohomology
import Colib.CategoryTheory.Sites.Hypercohomology.RestrictionDevissage

/-!
# Invertible restriction for finite motivic coefficients

When restriction along an actual smooth morphism is invertible for the
integral motivic complex in every degree, it is invertible for the cone
of multiplication by the coefficient level in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology.FreeYonedaUnivLE

universe w u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- An isomorphism on integral motivic cohomology in every degree is an
isomorphism with the actual finite cone coefficients. -/
theorem isIso_motivicFiniteCohomologyRestriction_of_integral
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) (q n : ℕ)
    (h : ∀ p : ℤ, IsIso (motivicCohomologyRestriction k p q f)) (p : ℤ) :
    IsIso (motivicFiniteCohomologyRestriction k p q n f) :=
  isIso_hypercohomologyPresheaf_map_mappingCone
    (SmoothSite.nisnevichTopology (Spec (.of k))) f (n • 𝟙 (motivicSheafComplex k q)) h h p

end AlgebraicGeometry.PresheafWithTransfers
