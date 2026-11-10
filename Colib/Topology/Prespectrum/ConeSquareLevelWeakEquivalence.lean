/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.ConeHomotopySquareFactorization
public import Colib.Topology.HomotopyCofiber.ReducedMappingConeWeakEquivalence

/-!
# Complete weakness of the original whole-track cone map at a fixed level

The actual reduced-cone weak theorem applies at an arbitrary original level, including zero.
The existing literal whole-track factorization then gives the same result for the original
mappingConeSquareMap. Only genuine HEP of the four points at this level and complete weak
side maps are required. No condition on other levels or replacement map is introduced.
-/
@[expose] public section
noncomputable section
open Topology TopCat
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Actual strict cone maps preserve complete weakness at any original well-based level. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeSquareLevelWeakEquivalence.lean:25-42"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem mappingConeMap_level_isWeakHomotopyEquivalence
    {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B) (n : ℕ)
    (hAL : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.left.point n))))
    (hAR : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.right.point n))))
    (hBL : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.left.point n))))
    (hBR : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.right.point n))))
    (hl : IsWeakHomotopyEquivalence (sq.left.map n))
    (hr : IsWeakHomotopyEquivalence (sq.right.map n)) :
    IsWeakHomotopyEquivalence ((mappingConeMap sq).map n) :=
  ReducedMappingCone.map_isWeakHomotopyEquivalence
    (A.left.point n) (A.right.point n) (A.hom.map n) (A.hom.map_point n)
    (B.left.point n) (B.right.point n) (B.hom.map n) (B.hom.map_point n)
    (sq.left.map n) (sq.right.map n) (sq.left.map_point n) (sq.right.map_point n)
    (fun x ↦ congrArg (fun h ↦ h.map n x) sq.w.symm) hAL hAR hBL hBR hl hr

/-- The unchanged whole-track cone map preserves complete weakness, including at level zero. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeSquareLevelWeakEquivalence.lean:45-67"
  "adaptation" "Original actual-map comparison with the native whole objects retained"]
theorem mappingConeSquareMap_level_isWeakHomotopyEquivalence
    {E F E' F' : LoopPrespectrum.{u}}
    (f : E ⟶ F) (g : E' ⟶ F') (a : E ⟶ E') (b : F ⟶ F')
    (H : Homotopy (f ≫ b) (a ≫ g)) (n : ℕ)
    (hE : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n))))
    (hF : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point n))))
    (hE' : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E'.point n))))
    (hF' : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F'.point n))))
    (ha : IsWeakHomotopyEquivalence (a.map n))
    (hb : IsWeakHomotopyEquivalence (b.map n)) :
    IsWeakHomotopyEquivalence ((mappingConeSquareMap f g a b H).map n) := by
  let sq₁ : Arrow.mk f ⟶ Arrow.mk (f ≫ b) := Arrow.homMk (𝟙 E) b (by simp)
  let sq₂ : Arrow.mk (a ≫ g) ⟶ Arrow.mk g := Arrow.homMk a (𝟙 F') (by simp)
  have h₁ := mappingConeMap_level_isWeakHomotopyEquivalence sq₁ n hE hF hE hF'
    (isWeakHomotopyEquivalence_id (E.space n)) hb
  have h₂ := mappingConeMap_level_isWeakHomotopyEquivalence sq₂ n hE hF' hE' hF'
    ha (isWeakHomotopyEquivalence_id (F'.space n))
  rw [mappingConeSquareMap_factor]
  exact h₂.comp ((mappingConeHomotopyMap_level_isWeakHomotopyEquivalence H n).comp h₁)

end Topology.LoopPrespectrum
