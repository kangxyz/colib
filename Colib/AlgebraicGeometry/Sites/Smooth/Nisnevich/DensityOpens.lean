/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.QuasiFinite.StandardDensity
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite

/-!
# The opens used to shrink a Nisnevich square

The base open avoids the closed bad images of the two side opens. Along the closed
complement it also avoids the closed bad image of the overlap. The resulting étale
open contains the entire preimage of the new closed complement and intersects the
overlap inside its prescribed open.

See [Voevodsky, Proposition 2.9](https://arxiv.org/pdf/0805.4576#page=6).
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Nisnevich

variable {W U V X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Choose the base open and the open of the étale side used to refine a
Nisnevich square, with the original open, étale, and overlap maps. -/
theorem exists_density_reducingOpens (a : W ⟶ U) (j : W ⟶ V) (i : U ⟶ X) (p : V ⟶ X)
    (h : a ≫ i = j ≫ p) [IsOpenImmersion i] [IsOpenImmersion j] [Etale p]
    [QuasiCompact i] [QuasiCompact j] [QuasiCompact p]
    {A : U.Opens} {D : V.Opens} {B : W.Opens} {d : ℕ}
    (hA : A.IsInStandardDensity (d + 1)) (hD : D.IsInStandardDensity (d + 1))
    (hB : B.IsInStandardDensity d) :
    ∃ (O : X.Opens) (T : V.Opens),
      O.IsInStandardDensity (d + 1) ∧ i ⁻¹ᵁ O ≤ A ∧ T ≤ p ⁻¹ᵁ O ∧ T ≤ D ∧
      j ⁻¹ᵁ T ≤ B ∧ ∀ v : V, p v ∈ O → p v ∉ i.opensRange → v ∈ T := by
  let q := j ≫ p
  let : LocallyQuasiFinite p := (locallyQuasiFinite_of_etale p).2
  let : LocallyQuasiFinite q := inferInstanceAs (LocallyQuasiFinite (j ≫ p))
  have hq : Set.range q ⊆ i.opensRange := by
    rintro _ ⟨w, rfl⟩
    exact ⟨a w, congrArg (fun g : W ⟶ X ↦ g w) h⟩
  let E := q.densityImageComplement B
  let O := (i.densityImageComplement A ⊓ p.densityImageComplement D) ⊓ (i.opensRange ⊔ E)
  let T := p ⁻¹ᵁ O ⊓ (p ⁻¹ᵁ E ⊔ j ''ᵁ B)
  refine ⟨O, T, ?_, ?_, inf_le_left, ?_, ?_, ?_⟩
  · exact ((i.isInStandardDensity_densityImageComplement hA).inf
      (p.isInStandardDensity_densityImageComplement hD)).inf
      (q.isInStandardDensity_sup_densityImageComplement hB i.opensRange hq)
  · intro u hu
    exact i.preimage_densityImageComplement_le A hu.1.1
  · intro v hv
    exact p.preimage_densityImageComplement_le D hv.1.1.2
  · intro w hw
    rcases hw.2 with hw | ⟨w', hw', hww'⟩
    · exact q.preimage_densityImageComplement_le B hw
    · exact (j.isOpenEmbedding.injective hww') ▸ hw'
  · intro v hv hvi
    exact ⟨hv, Or.inl (hv.2.resolve_left hvi)⟩

end AlgebraicGeometry.Nisnevich
