/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.GTheory.Dedekind.FiniteResidue
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic

/-! # The original arithmetic integer consumer of finite-residue G₂ injectivity -/

public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped nonZeroDivisors

namespace ColibTest.DedekindFiniteResidue

/-- Actual integer height-one residue fields are finite by finite integer
quotients and the original quotient-to-residue algebra equivalence. -/
theorem integerResidueFinite (p : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Finite p.asIdeal.ResidueField := by
  let : Finite (ℤ ⧸ p.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  exact Finite.of_surjective (FGModuleCat.DedekindResidue.quotientResidueFieldAlgEquiv ℤ p)
    (FGModuleCat.DedekindResidue.quotientResidueFieldAlgEquiv ℤ p).surjective

example : Function.Injective (FGModuleCat.Localization.localizationKMap.{0, 0} (nonZeroDivisors ℤ)
    2) :=
  FGModuleCat.DedekindFiniteResidue.genericGTwo_injective ℤ integerResidueFinite

end ColibTest.DedekindFiniteResidue
