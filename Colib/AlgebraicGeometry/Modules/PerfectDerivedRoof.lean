/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.CommonRightFraction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone

/-!
# Chain-map representatives of native perfect derived roofs

A derived roof with a native perfect source can be represented by two actual chain maps from a
native perfect complex, retaining both target complexes. If the denominator is invertible after
open restriction, its chain-map representative is a quasi-isomorphism on that open. The specified
restricted derived morphism is retained through the canonical comparison with degreewise
restriction.

This is a representative comparison. The existence of the geometric derived roof is a separate
input here; this file does not assert a strict factorization of an outgoing chain map (App2).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u d₁ d₂

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d₁} X.Modules] [HasDerivedCategory.{d₂} U.Modules]

/-- Represent a perfect derived roof by actual chain maps, with a quasi-isomorphism after
restriction and the original restricted derived morphism. The source is perfect in the native
local sense, with no global strictly perfect or projective representative assumption. -/
theorem exists_isPerfectComplex_chainMap_roof
    {R K E : CochainComplex X.Modules ℤ}
    (hR : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R)
    (s : DerivedCategory.Q.obj R ⟶ DerivedCategory.Q.obj K)
    (t : DerivedCategory.Q.obj R ⟶ DerivedCategory.Q.obj E)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))
    (hs : IsIso ((restrictFunctor j).mapDerivedCategory.map s))
    (ht : (restrictFunctor j).mapDerivedCategory.map s ≫
        (restrictFunctor j).mapDerivedCategoryFactors.hom.app K ≫ α =
      (restrictFunctor j).mapDerivedCategory.map t ≫
        (restrictFunctor j).mapDerivedCategoryFactors.hom.app E) :
    ∃ (R' : CochainComplex X.Modules ℤ) (q : R' ⟶ K) (a : R' ⟶ E),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R' ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
  let F := restrictFunctor j
  let L := F.mapDerivedCategory
  let e := F.mapDerivedCategoryFactors
  obtain ⟨R', r, q, a, hr, hq, ha⟩ := DerivedCategory.exists_common_right_fraction s t
  have hR' : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R' :=
    (RingedSpace.isPerfectComplex_iff_of_quasiIso r hr).2 hR
  have hq' : L.map (DerivedCategory.Q.map q) =
      L.map (DerivedCategory.Q.map r) ≫ L.map s := by
    rw [← hq, Functor.map_comp]
  have : IsIso (L.map (DerivedCategory.Q.map q)) := by
    rw [hq']
    infer_instance
  have hq'' : DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) =
      e.inv.app R' ≫ L.map (DerivedCategory.Q.map q) ≫ e.hom.app K := by
    rw [F.mapDerivedCategoryFactors_hom_naturality]
    simp [e]
  have hqa : IsIso (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) := by
    rw [hq'']
    infer_instance
  refine ⟨R', q, a, hR', (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hqa, ?_⟩
  apply (cancel_epi (e.hom.app R')).1
  change e.hom.app R' ≫ DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫ α =
    e.hom.app R' ≫ DerivedCategory.Q.map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a)
  rw [← F.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← F.mapDerivedCategoryFactors_hom_naturality, hq', Category.assoc, ht,
    ← L.map_comp_assoc, ha]

end AlgebraicGeometry.Scheme.Modules
