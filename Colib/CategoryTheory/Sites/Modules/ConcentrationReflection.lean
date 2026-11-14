/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Reflection of concentration through faithful exact coefficient forgetting

This auxiliary result requires exactness and faithfulness of
an underived functor only. It does not assert fullness on derived categories.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace CochainComplex

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [F.Faithful]
variable (K : CochainComplex C ℤ)

/-- An exact faithful coefficient forgetful functor reflects exactness in each degree. -/
theorem exactAt_of_exactAt_forget (i : ℤ)
    (h : ((F.mapHomologicalComplex (.up ℤ)).obj K).ExactAt i) : K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  apply ((K.sc i).exact_map_iff_of_faithful F).mp
  change ((K.sc i).map F).Exact at h
  exact h

/-- Reflection of the lower cohomological bound. -/
theorem isGE_of_forget (n : ℤ)
    [CochainComplex.IsGE ((F.mapHomologicalComplex (.up ℤ)).obj K) n] : K.IsGE n := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact exactAt_of_exactAt_forget F K i
    (CochainComplex.exactAt_of_isGE ((F.mapHomologicalComplex (.up ℤ)).obj K) n i hi)

/-- Reflection of the upper cohomological bound. -/
theorem isLE_of_forget (n : ℤ)
    [CochainComplex.IsLE ((F.mapHomologicalComplex (.up ℤ)).obj K) n] : K.IsLE n := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact exactAt_of_exactAt_forget F K i
    (CochainComplex.exactAt_of_isLE ((F.mapHomologicalComplex (.up ℤ)).obj K) n i hi)

end CochainComplex
