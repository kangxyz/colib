/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Functoriality

/-!
# Additive functors and finite-coefficient cones

An additive functor commutes with the actual cone of multiplication by a natural
number. Its comparison preserves the integral map and the signed connecting
morphism, using the native comparison for cochain shifts. The comparison itself
is reexported from `FiniteCoefficients.Functoriality`; only the compatibility
equations are added here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.finiteCoefficients

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C] [Preadditive D] [HasBinaryBiproducts D]

private theorem inr_eqToIso {K L : CochainComplex D ℤ} {φ ψ : K ⟶ L} (h : φ = ψ) :
    mappingCone.inr φ ≫ (eqToIso (congrArg (fun f : K ⟶ L ↦ mappingCone f) h)).hom =
      mappingCone.inr ψ := by
  subst ψ
  simp

private theorem eqToIso_δ {K L : CochainComplex D ℤ} {φ ψ : K ⟶ L} (h : φ = ψ) :
    (eqToIso (congrArg (fun f : K ⟶ L ↦ mappingCone f) h)).hom ≫
        (mappingCone.triangle ψ).mor₃ = (mappingCone.triangle φ).mor₃ := by
  subst ψ
  simp

variable (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) (n : ℕ)

/-- The comparison preserves the original integral-to-finite coefficient map. -/
theorem mapIso_integral :
    (F.mapHomologicalComplex (.up ℤ)).map (integral K n) ≫ (mapIso F K n).hom =
      integral ((F.mapHomologicalComplex (.up ℤ)).obj K) n := by
  rw [mapIso_eq F K n (by simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id])]
  dsimp only [Iso.trans_hom, integral]
  rw [← Category.assoc, mappingCone.map_inr]
  exact inr_eqToIso (by simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id])

/-- The comparison preserves the connecting map, including its signed shift. -/
theorem mapIso_bockstein :
    (F.mapHomologicalComplex (.up ℤ)).map (bockstein K n) ≫
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app K =
      (mapIso F K n).hom ≫ bockstein ((F.mapHomologicalComplex (.up ℤ)).obj K) n := by
  dsimp only [bockstein, triangle]
  rw [mappingCone.map_δ]
  rw [mapIso_eq F K n (by simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id])]
  dsimp only [Iso.trans_hom]
  rw [Category.assoc, eqToIso_δ]
  simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id]

end CochainComplex.finiteCoefficients
