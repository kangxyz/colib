/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleKummerTrace
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Trace compatibility of the restricted Kummer extension class

The actual restriction comparisons identify the Kummer complexes. The native trace
commutes with their extension classes. No identification with algebraic norm is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
universe u w
namespace Stacks.EtaleCohomology
open Stacks.Kummer
variable {S Y : Scheme.{u}} (g : Y ⟶ S) [Etale g]

/-- The actual Gm restriction comparison commutes with the power map. -/
theorem restrictionMultiplicative_comm_powMap (n : ℕ) :
    (etaleRestriction.{u, 0} g).map (powMap.{u, 0} S n) ≫
        (etaleRestrictionMultiplicativeSheafIso g).hom =
      (etaleRestrictionMultiplicativeSheafIso g).hom ≫ powMap.{u, 0} Y n := by
  simp [powMap]

/-- The mu_n comparison is the induced isomorphism of genuine kernels. -/
def etaleRestrictionRootsOfUnityIso (n : ℕ) :
    (etaleRestriction.{u, 0} g).obj (rootsOfUnitySheaf.{u, 0} S n) ≅
      rootsOfUnitySheaf.{u, 0} Y n :=
  PreservesKernel.iso (etaleRestriction.{u, 0} g) (powMap.{u, 0} S n) ≪≫
    kernel.mapIso _ (powMap.{u, 0} Y n)
      (etaleRestrictionMultiplicativeSheafIso g)
      (etaleRestrictionMultiplicativeSheafIso g)
      (restrictionMultiplicative_comm_powMap g n)

set_option backward.isDefEq.respectTransparency false in
/-- Compare the actual restricted sequence to the Kummer sequence on Y. -/
def etaleRestrictionKummerIso (n : ℕ) :
    (kummerSequence.{u, 0} S n).map (etaleRestriction.{u, 0} g) ≅
      kummerSequence.{u, 0} Y n :=
  ShortComplex.isoMk (etaleRestrictionRootsOfUnityIso g n)
    (etaleRestrictionMultiplicativeSheafIso g)
    (etaleRestrictionMultiplicativeSheafIso g)
    (by
      dsimp only [etaleRestrictionRootsOfUnityIso, Iso.trans_hom,
        kummerSequence, ShortComplex.kernelSequence, ShortComplex.map]
      rw [Category.assoc, kernel.mapIso_hom, kernel.lift_ι,
        ← Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι])
    (restrictionMultiplicative_comm_powMap g n).symm

variable [IsFinite g]
variable [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Actual connecting-class trace identity for the pushed restricted sequence.
No norm map, commutative square, or desired compatibility is an input assumption. -/
theorem restrictedKummerTrace_extClass {n : ℕ} (hn0 : n ≠ 0)
    (hS : IsUnit ((n : ℕ) : Γ(S, ⊤))) :
    ((kummerSequence_shortExact.{u, 0} S hn0 hS).map_of_exact
        (etaleRestriction.{u, 0} g ⋙ etaleAbelianDirectImage.{u, 0} g)).extClass.comp
      (Ext.mk₀ (finiteEtaleTrace g (rootsOfUnitySheaf.{u, 0} S n))) (add_zero 1) =
    (Ext.mk₀ (finiteEtaleTrace g (multiplicativeSheaf.{u, 0} S))).comp
      (kummerSequence_shortExact.{u, 0} S hn0 hS).extClass (zero_add 1) :=
  ShortComplex.ShortExact.extClass_naturality
    ((kummerSequence_shortExact.{u, 0} S hn0 hS).map_of_exact
      (etaleRestriction.{u, 0} g ⋙ etaleAbelianDirectImage.{u, 0} g))
    (kummerSequence_shortExact.{u, 0} S hn0 hS)
    (restrictedKummerTraceMorphism g n)

end Stacks.EtaleCohomology
end
