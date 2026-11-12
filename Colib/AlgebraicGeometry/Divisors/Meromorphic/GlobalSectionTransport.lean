/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalSection
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport

/-!
# Naturality of the meromorphic image of an ordinary section

The generic-germ construction commutes with the original module morphism. This
identifies an ordinary transported numerator with its existing meromorphic image.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X] (L N : X.Modules)
  [L.IsQuasicoherent] [N.IsQuasicoherent]

/-- The generic value of a transported meromorphic section is the image under the
actual generic stalk map. -/
theorem meromorphicGenericValue_mapMeromorphicSection (f : L ⟶ N)
    (s : MeromorphicSection X.sheaf L) :
    meromorphicGenericValue X N (mapMeromorphicSection L N f s) =
      stalkLinearMap L N f (genericPoint X) (meromorphicGenericValue X L s) := by
  apply meromorphicGenericValue_eq
  exact (meromorphicSectionSheafIsoConstant_naturality_apply L N f s ⊤).symm.trans
    ((congrArg ((constantGenericStalkModuleMap L N f).val.app (op ⊤))
      (constantGenericStalkModuleSection_meromorphicGenericValue X L s)).trans
      (constantGenericStalkModuleMap_section L N f ⊤ _))

/-- The meromorphic image of an ordinary section commutes with its literal module map. -/
theorem meromorphicSectionOfGlobalSection_map (f : L ⟶ N) (s : Γ(L, ⊤)) :
    meromorphicSectionOfGlobalSection N (f.app ⊤ s) =
      mapMeromorphicSection L N f (meromorphicSectionOfGlobalSection L s) := by
  apply meromorphicGenericValue_injective X N
  rw [meromorphicGenericValue_meromorphicSectionOfGlobalSection,
    meromorphicGenericValue_mapMeromorphicSection,
    meromorphicGenericValue_meromorphicSectionOfGlobalSection]
  exact (stalkLinearMap_germ L N f ⊤ (genericPoint X) trivial s).symm

end AlgebraicGeometry
