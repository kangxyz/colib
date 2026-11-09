/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedJoint
public import Colib.AlgebraicGeometry.Modules.PerfectKernel

/-!
# Supported perfect complexes and actual exact sequences

Support is invariant under roofs of genuine quasi-isomorphisms, in every chosen
model of the derived category. Exact restriction and native perfect triangle
closure retain all three original terms of a short exact sequence. These lemmas
require no compactness or separation assumptions.

Adapted from Quillen's `PerfectComplexes/Support/Closure.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Stacks perfectness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u d

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- A genuine quasi-isomorphism preserves support in both directions. -/
theorem perfectSupported_iff_of_quasiIso {K L : CochainComplex X.Modules ℤ}
    (f : K ⟶ L) [QuasiIso f] : perfectSupported j K ↔ perfectSupported j L := by
  apply and_congr (RingedSpace.isPerfectComplex_iff_of_quasiIso f inferInstance)
  exact forall_congr' fun n => exactAt_iff_of_quasiIsoAt
    (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map f) n

/-- Support descends across an actual roof of quasi-isomorphisms. -/
theorem perfectSupported_iff_of_quasiIsoRoof {K L : CochainComplex X.Modules ℤ}
    (h : CochainComplex.QuasiIsoRoof K L) : perfectSupported j K ↔ perfectSupported j L := by
  obtain ⟨M, f, s, hf, hs⟩ := CochainComplex.quasiIsoRoof_iff.1 h
  exact (perfectSupported_iff_of_quasiIso j f).trans
    (perfectSupported_iff_of_quasiIso j s).symm

/-- Derived isomorphisms preserve actual supported complexes in any derived model. -/
theorem perfectSupported_iff_of_derivedIso [HasDerivedCategory.{d} X.Modules]
    {K L : CochainComplex X.Modules ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    perfectSupported j K ↔ perfectSupported j L :=
  perfectSupported_iff_of_quasiIsoRoof j
    ((CochainComplex.quasiIsoRoof_iff_nonempty_iso K L).2 ⟨e⟩)

/-- The actual first term of a short exact sequence retains prescribed support. -/
theorem perfectSupported_X₁_of_shortExact
    {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact)
    (h₂ : perfectSupported j S.X₂) (h₃ : perfectSupported j S.X₃) :
    perfectSupported j S.X₁ := by
  refine ⟨RingedSpace.isPerfectComplex_X₁_of_shortExact X.toRingedSpace hS h₂.1 h₃.1, ?_⟩
  let R := (restrictFunctor j).mapHomologicalComplex (.up ℤ)
  apply (hS.map_of_exact R).acyclic_X₁
  rw [quasiIso_iff]
  exact fun n => (quasiIsoAt_iff_exactAt _ n (h₂.2 n)).2 (h₃.2 n)

/-- The actual middle term of a short exact sequence retains prescribed support. -/
theorem perfectSupported_X₂_of_shortExact
    {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : perfectSupported j S.X₁) (h₃ : perfectSupported j S.X₃) :
    perfectSupported j S.X₂ :=
  ⟨RingedSpace.isPerfectComplex_X₂_of_shortExact X.toRingedSpace hS h₁.1 h₃.1,
    (hS.map_of_exact ((restrictFunctor j).mapHomologicalComplex (.up ℤ))).acyclic_X₂
      h₁.2 h₃.2⟩

/-- The actual last term of a short exact sequence retains prescribed support. -/
theorem perfectSupported_X₃_of_shortExact
    {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : perfectSupported j S.X₁) (h₂ : perfectSupported j S.X₂) :
    perfectSupported j S.X₃ := by
  refine ⟨RingedSpace.isPerfectComplex_X₃_of_shortExact hS h₁.1 h₂.1, ?_⟩
  let R := (restrictFunctor j).mapHomologicalComplex (.up ℤ)
  apply (hS.map_of_exact R).acyclic_X₃
  rw [quasiIso_iff]
  exact fun n => (quasiIsoAt_iff_exactAt _ n (h₁.2 n)).2 (h₂.2 n)

/-- The categorical kernel of an actual epimorphism retains prescribed support. -/
theorem perfectSupported_kernel_of_epi {K L : CochainComplex X.Modules ℤ}
    (hK : perfectSupported j K) (hL : perfectSupported j L) (f : K ⟶ L) [Epi f] :
    perfectSupported j (kernel f) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact f }
  exact perfectSupported_X₁_of_shortExact j hS hK hL

end AlgebraicGeometry.Scheme.Modules
