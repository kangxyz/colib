/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.AmbientIntersection
public import Colib.Algebra.Category.ModuleCat.Annihilator
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionMultiplicity
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length

/-!
# The original pair incidence acts on its actual ambient Tor

Both original stalk-map kernels annihilate the native Tor module. The actual incidence
kernel is their sum, so the quotient-module action descends to the full original incidence
local ring. The scalar equation identifies restriction with the original ambient action.
No regular list, replacement module, reduction, flatness or comparison equality is assumed.

This is the original pair coefficient needed for full-exterior flat base change. Changing
scalars along this surjective closed-immersion stalk map preserves length. This is distinct
from flat exterior base change, whose closed-fibre length factor must still be retained.

The algebraic suppliers are native Tor annihilation and symmetry (Stacks 00M3), Mathlib's
`Module.IsTorsionBySet.module`, and the native first isomorphism theorem. The scheme-theoretic
sum is `correspondenceIncidenceAmbientInclusion_ker`, not a radical intersection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The original four-factor ambient local ring at a pair-incidence point. -/
abbrev correspondenceIncidenceAmbientStalk (x : correspondenceIncidence f g h z w) :=
  (correspondenceIntersectionAmbient f g h).presheaf.stalk
    (correspondenceIncidenceAmbientInclusion f g h z w x)

/-- Native Tor of the original two actual structure-ring modules. -/
abbrev correspondenceIncidenceAmbientTor (x : correspondenceIncidence f g h z w) (n : ℕ) :
    ModuleCat (correspondenceIncidenceAmbientStalk f g h z w x) :=
  ((Tor (ModuleCat (correspondenceIncidenceAmbientStalk f g h z w x)) n).obj
    (correspondenceIncidenceSupportStalkModule f g h z w x)).obj
      (correspondenceIncidenceTripleStalkModule f g h z w x)

/-- The full original incidence kernel annihilates each original ambient Tor degree. -/
theorem correspondenceIncidence_ker_le_annihilator_tor [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    RingHom.ker ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom ≤
      Module.annihilator (correspondenceIncidenceAmbientStalk f g h z w x)
        (correspondenceIncidenceAmbientTor f g h z w x n) := by
  let A := correspondenceIncidenceAmbientStalk f g h z w x
  let M : ModuleCat A := correspondenceIncidenceSupportStalkModule f g h z w x
  let N : ModuleCat A := correspondenceIncidenceTripleStalkModule f g h z w x
  let φ : A →+* (correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w x) :=
    (((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceIncidence_ambient_point_eq f g h z w x))).hom ≫
      (correspondenceSupportProductInclusion f g h z w).stalkMap
        (correspondenceIncidenceToSupportProduct f g h z w x)).hom
  let ψ : A →+* (correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w x) :=
    ((correspondenceTripleInclusion f g h).stalkMap
    (correspondenceIncidenceInclusion f g h z w x)).hom
  have hφ : RingHom.ker φ = IdealSheafData.stalk
      (correspondenceSupportProductInclusion f g h z w).ker
        (correspondenceIncidenceAmbientInclusion f g h z w x) := by
    have aux (p : correspondenceIntersectionAmbient f g h)
        (hp : p = correspondenceSupportProductInclusion f g h z w
          (correspondenceIncidenceToSupportProduct f g h z w x)) :
        RingHom.ker (((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
          (Inseparable.of_eq hp)).hom ≫
            (correspondenceSupportProductInclusion f g h z w).stalkMap
              (correspondenceIncidenceToSupportProduct f g h z w x)).hom =
          IdealSheafData.stalk (correspondenceSupportProductInclusion f g h z w).ker p := by
      subst p
      simpa [TopCat.Presheaf.stalkCongr] using
        ker_stalkMap_eq_idealStalk_ker (correspondenceSupportProductInclusion f g h z w)
          (correspondenceIncidenceToSupportProduct f g h z w x)
    exact aux _ (correspondenceIncidence_ambient_point_eq f g h z w x)
  have hψ : RingHom.ker ψ = IdealSheafData.stalk (correspondenceTripleInclusion f g h).ker
      (correspondenceIncidenceAmbientInclusion f g h z w x) :=
    ker_stalkMap_eq_idealStalk_ker (correspondenceTripleInclusion f g h)
      (correspondenceIncidenceInclusion f g h z w x)
  rw [ker_stalkMap_eq_idealStalk_ker, correspondenceIncidenceAmbientInclusion_ker,
    IdealSheafData.stalk_sup, ← hφ, ← hψ]
  apply sup_le
  · intro a ha
    let e : correspondenceIncidenceAmbientTor f g h z w x n ≅
        ((Tor (ModuleCat A) n).obj N).obj M :=
      (((Tor_iso_Tor' A n) ≪≫ (torFlip_iso_Tor' A n).symm).app M).app N
    apply mem_annihilator_of_moduleCat_iso e.symm
    apply mem_annihilator_tor_of_mem_annihilator N M n
    exact ModuleCat.ker_le_annihilator_restrictScalars ψ _ ha
  · intro a ha
    apply mem_annihilator_tor_of_mem_annihilator M N n
    exact ModuleCat.ker_le_annihilator_restrictScalars φ _ ha

/-- The literal original pair-incidence local ring acts on its native ambient Tor. -/
@[instance_reducible]
def correspondenceIncidenceTorModule [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    Module ((correspondenceIncidence f g h z w).presheaf.stalk x)
      (correspondenceIncidenceAmbientTor f g h z w x n) := by
  let hkill := (Module.isTorsionBySet_iff_subset_annihilator
    (correspondenceIncidenceAmbientStalk f g h z w x)
    (correspondenceIncidenceAmbientTor f g h z w x n)).mpr
    (correspondenceIncidence_ker_le_annihilator_tor f g h z w x n)
  letI := hkill.module
  exact Module.compHom _ (RingHom.quotientKerEquivOfSurjective
    (SurjectiveOnStalks.stalkMap_surjective
      (correspondenceIncidenceAmbientInclusion f g h z w) x)).symm.toRingHom

/-- Every ambient scalar acts through the original incidence stalk map, with no chosen action. -/
theorem correspondenceIncidenceTorModule_stalkMap_smul [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ)
    (a : correspondenceIncidenceAmbientStalk f g h z w x)
    (m : correspondenceIncidenceAmbientTor f g h z w x n) :
    letI := correspondenceIncidenceTorModule f g h z w x n
    ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom a • m = a • m := by
  let hkill := (Module.isTorsionBySet_iff_subset_annihilator
    (correspondenceIncidenceAmbientStalk f g h z w x)
    (correspondenceIncidenceAmbientTor f g h z w x n)).mpr
    (correspondenceIncidence_ker_le_annihilator_tor f g h z w x n)
  let := hkill.module
  change (RingHom.quotientKerEquivOfSurjective
    (SurjectiveOnStalks.stalkMap_surjective
      (correspondenceIncidenceAmbientInclusion f g h z w) x)).symm
        (((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom a) • m = a • m
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

/-- The quotient-induced action is an actual scalar tower over the original stalk map. -/
theorem correspondenceIncidenceTorScalarTower [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    let := correspondenceIncidenceTorModule f g h z w x n
    let := ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom.toAlgebra
    IsScalarTower (correspondenceIncidenceAmbientStalk f g h z w x)
      ((correspondenceIncidence f g h z w).presheaf.stalk x)
      (correspondenceIncidenceAmbientTor f g h z w x n) := by
  let := correspondenceIncidenceTorModule f g h z w x n
  let := ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom.toAlgebra
  refine ⟨fun a b m => ?_⟩
  change (((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom a * b) • m =
    a • (b • m)
  rw [mul_smul, correspondenceIncidenceTorModule_stalkMap_smul]

/-- The original pair coefficient has the same length over its ambient and incidence stalks. -/
theorem correspondenceIncidenceTor_length_eq_incidence [IsSeparated g]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    let := correspondenceIncidenceTorModule f g h z w x n
    Module.length (correspondenceIncidenceAmbientStalk f g h z w x)
      (correspondenceIncidenceAmbientTor f g h z w x n) =
        Module.length ((correspondenceIncidence f g h z w).presheaf.stalk x)
          (correspondenceIncidenceAmbientTor f g h z w x n) := by
  let := correspondenceIncidenceTorModule f g h z w x n
  let := ((correspondenceIncidenceAmbientInclusion f g h z w).stalkMap x).hom.toAlgebra
  let := correspondenceIncidenceTorScalarTower f g h z w x n
  exact Module.length_eq_of_surjective (SurjectiveOnStalks.stalkMap_surjective
    (correspondenceIncidenceAmbientInclusion f g h z w) x)

end Stacks.Chow
