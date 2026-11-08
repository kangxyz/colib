/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupport
public import Mathlib.Topology.Sheaves.Abelian

/-! # Stalkwise detection of actual supported restriction

Acyclicity is tested on the abelian stalks of the actual homology sheaves. The
native homology comparison for exact restriction and its native stalk comparison
identify the test with vanishing at the image points. No perfectness, compactness,
quasicoherence or separation hypothesis is needed. This replaces the derived-zero
proof in Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/
RestrictionVanishing.lean at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A module sheaf vanishes exactly when all of its underlying abelian stalks vanish. -/
theorem isZero_iff_stalk_isZero {X : Scheme.{u}} (M : X.Modules) :
    IsZero M ↔ ∀ x : X,
      IsZero ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M) := by
  let F := _root_.SheafOfModules.toSheaf X.ringCatSheaf
  constructor
  · intro h x
    exact (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_isZero h
  · intro h
    have hz : IsZero (F.obj M) :=
      (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (F.obj M)).2 h
    rw [IsZero.iff_id_eq_zero]
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact hz.eq_of_src (𝟙 _) 0

/-- Exact open restriction vanishes precisely at the image stalks of each homology sheaf. -/
theorem restrictAcyclic_iff_stalkHomology {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ) :
    (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic ↔
      ∀ (n : ℤ) (x : U),
        IsZero ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j x)).obj
          (K.homology n)) := by
  change (∀ n, _ ) ↔ _
  apply forall_congr'
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let e : (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n ≅
      (restrictFunctor j).obj (K.homology n) :=
    (K.sc n).mapHomologyIso (restrictFunctor j)
  rw [e.isZero_iff, isZero_iff_stalk_isZero]
  apply forall_congr'
  intro x
  exact ((restrictStalkNatIso j x).app (K.homology n)).isZero_iff

/-- Actual restriction to an inverse-image open preserves the prescribed acyclicity. -/
theorem restrictAcyclic_preimage {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (T : X.Opens) (K : CochainComplex X.Modules ℤ)
    (h : (((restrictFunctor T.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic) :
    (((restrictFunctor (j ⁻¹ᵁ T).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).Acyclic := by
  rw [restrictAcyclic_iff_stalkHomology] at h ⊢
  intro n x
  let e : (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n ≅
      (restrictFunctor j).obj (K.homology n) :=
    (K.sc n).mapHomologyIso (restrictFunctor j)
  let F := toPresheaf U ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((j ⁻¹ᵁ T).ι x)
  apply ((F.mapIso e).isZero_iff).2
  apply (((restrictStalkNatIso j ((j ⁻¹ᵁ T).ι x)).app (K.homology n)).isZero_iff).2
  exact h n ⟨j x.val, x.property⟩

end AlgebraicGeometry.Scheme.Modules
