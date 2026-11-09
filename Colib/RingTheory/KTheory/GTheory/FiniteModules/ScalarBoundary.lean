/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Algebra.Category.FGModuleCat.LocalizationLinear
public import Colib.KTheory.Quillen.LowDegreeScalarAction.SmallModelBoundary
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization

/-!
# Scalar operations and the original finite-module localization boundary

For any multiplicative set in a commutative Noetherian ring, the unchanged
Serre connecting map sends the degree-one scalar operation to the inverse
supported degree-zero operation. Both use the actual lifted scalar natural
automorphisms in the original chosen small exact models. The sign comes from
the genuine fiber-track and loop-shift calculation, not a supplied boundary law.

Implementation provenance: the finite-module clauses of
`Quillen/KTheory/LowDegreeScalarAction/SmallModelBoundary.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native finite-module theorem
uses its already-installed abelian exact structure and original boundary.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.ExactCategory
open scoped ModuleCat.Algebra
universe u v
namespace FGModuleCat.Localization

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R]
  (S : Submonoid R)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual supported operation restricts the lifted base-ring scalar automorphism. -/
def supportedScalarKZeroAction : Rˣ →* (SupportedG.{u, v} S 0 →* SupportedG.{u, v} S 1) :=
  SmallModelBoundary.supportedKZeroAction (localizationExactFunctor S) R

/-- The unchanged native finite-module boundary has the original negative scalar sign. -/
theorem connectingHom_scalar (r : Rˣ)
    (a : FractionLocalization.G.{u, v} (Localization S) 1) :
    connectingHom S 1
        (ScalarUnit.smallModelKOneAction R
          (abelianExactStructure (FGModuleCat.{v} (Localization S))) r a) =
      (supportedScalarKZeroAction S r (connectingHom S 0 a))⁻¹ :=
  SmallModelBoundary.connectingHom_scalar (localizationExactFunctor S) R r a

end FGModuleCat.Localization

attribute [colib_ref "quillen"
  "Quillen/KTheory/LowDegreeScalarAction/SmallModelBoundary.lean:203-241"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  FGModuleCat.Localization.supportedScalarKZeroAction
  FGModuleCat.Localization.connectingHom_scalar

attribute [colib_tag "COL-0377"]
  FGModuleCat.Localization.connectingHom_scalar
