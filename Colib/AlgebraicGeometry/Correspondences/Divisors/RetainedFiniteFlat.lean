/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Divisors.FiniteFlat
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.BoundaryFiniteFlat

/-!
# Whole finite locally free divisors on the retained open

An original closed subscheme supported in the retained open is isomorphic to its full
scheme-theoretic inverse image. This transports the existing finite locally free structure
from the compactification to the original source projection of the correspondence. The
resulting native correspondence retains all stalk lengths and residue degrees.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] Stacks.Morphisms.IsFiniteLocallyFree.isFinite
  Stacks.Morphisms.IsFiniteLocallyFree.flat
  Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {C U V : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
  (I : C.IdealSheafData) (hI : Set.range I.subschemeι ⊆ Set.range j)

/-- The original whole closed scheme equals its restriction up to the canonical pullback iso. -/
def retainedSubschemeIso : (I.comap j).subscheme ≅ I.subscheme :=
  I.comapIso j ≪≫ (IsOpenImmersion.isPullback_lift_id I.subschemeι j hI).isoPullback.symm

@[reassoc]
theorem retainedSubschemeIso_hom_subschemeι :
    (retainedSubschemeIso j I hI).hom ≫ I.subschemeι = (I.comap j).subschemeι ≫ j := by
  dsimp only [retainedSubschemeIso, Iso.trans_hom, Iso.symm_hom]
  have h := (IsOpenImmersion.isPullback_lift_id I.subschemeι j hI).isoPullback_inv_snd
  simp only [Category.comp_id] at h
  rw [Category.assoc, h, ← pullback.condition,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

include hI in
/-- Finite local freeness is retained by the actual whole closed subscheme, without reduction. -/
@[colib_tag "COL-1072"]
theorem isFiniteLocallyFree_comap_of_range_subset (q : C ⟶ V)
    [Stacks.Morphisms.IsFiniteLocallyFree (I.subschemeι ≫ q)] :
    Stacks.Morphisms.IsFiniteLocallyFree ((I.comap j).subschemeι ≫ j ≫ q) := by
  have he : (I.comap j).subschemeι ≫ j ≫ q =
      (retainedSubschemeIso j I hI).hom ≫ (I.subschemeι ≫ q) := by
    exact (retainedSubschemeIso_hom_subschemeι_assoc j I hI q).symm
  rw [he]
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Chow

variable {C U V Y S : Scheme.{u}} [IsNoetherian U]
  (p : V ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
  (q : C ⟶ V) (j : U ⟶ C) [IsOpenImmersion j]
  (r : U ⟶ pullback p t) (hr : r ≫ pullback.fst p t = j ≫ q)
  (I : C.IdealSheafData) (hI : Set.range I.subschemeι ⊆ Set.range j)
  [Stacks.Morphisms.IsFiniteLocallyFree (I.subschemeι ≫ q)]

include hr hI in
omit [AlgebraicGeometry.IsNoetherian U] [IsSeparated t] [LocallyOfFiniteType t] in
/-- The literal first projection of the restricted whole divisor is finite locally free. -/
theorem retainedDivisor_firstProjection_finiteLocallyFree :
    Stacks.Morphisms.IsFiniteLocallyFree (((I.comap j).subschemeι ≫ r) ≫ pullback.fst p t) := by
  rw [Category.assoc, hr]
  exact Scheme.IdealSheafData.isFiniteLocallyFree_comap_of_range_subset j I hI q

/-- The native correspondence obtained from the original whole finite locally free divisor. -/
@[colib_tag "COL-1072"]
def retainedFiniteFlatDivisorCorrespondence : finiteCorrespondences p t :=
  let := retainedDivisor_firstProjection_finiteLocallyFree p t q j r hr I hI
  finiteFlatDivisorCorrespondence p t r (I.comap j)

local instance retainedDivisorNoetherian (J : U.IdealSheafData) : IsNoetherian J.subscheme :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace J.subschemeι }

/-- Its value is the original whole restricted zero scheme's residue-weighted fundamental cycle. -/
theorem retainedFiniteFlatDivisorCorrespondence_val :
    (retainedFiniteFlatDivisorCorrespondence p t q j r hr I hI).val =
      noetherianCyclePushforward ((I.comap j).subschemeι ≫ r)
        (AlgebraicCycle.fundamentalCycle (I.comap j).subscheme) := by
  have := retainedDivisor_firstProjection_finiteLocallyFree p t q j r hr I hI
  have : IsFinite ((I.comap j).subschemeι ≫ r) := IsFinite.of_comp _ (pullback.fst p t)
  exact congrArg (fun F => F (AlgebraicCycle.fundamentalCycle (I.comap j).subscheme))
    (noetherianCyclePushforward_eq_finiteCyclePushforward ((I.comap j).subschemeι ≫ r)).symm

end Stacks.Chow
