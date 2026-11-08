/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorModule
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import Colib.RingTheory.Koszul.CoefficientFunctor
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The actual finite Tor module localizes to its sheaf stalk

The coefficient is the global sections of the actual original Tor sheaf on the
whole finite model. Native affine germ localization identifies its localization
with its actual sheaf stalk, linearly over the localized coordinate ring. The
stalk scalar action is transported along the native localization algebra
isomorphism; its composite on original global sections is exactly the germ map.
Consequently the comparison applies inside the remaining Koszul complex, not
merely after taking module lengths.

The proof uses the pinned native `isLocalizedModule_germₗ` and Mathlib's
`IsLocalizedModule.iso` and `extendScalarsOfIsLocalization`. It preserves the
nonreduced whole finite model and every original Tor degree. No flatness of the
finite image map, finite length, or supplied coefficient comparison is assumed.
The subsequent comparison with the original sixfold stalk and original ordered
Z-list remains a separate geometric scalar compatibility statement.

Implementation source: independent motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
`Correspondences/Composition/Cycles/FirstStageWeightedRemainingCoefficient.lean`.
This file supplies the affine-localization ingredient, not that complete result.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [IsSeparated g] [IsSeparated h]
  [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : correspondenceLeftImageIncidence f g h i z w v)
  (q : correspondenceRemainingFiniteModel f g h i z w v x)

local notation3 (prettyPrint := false) "E" => correspondenceRemainingFiniteModel f g h i z w v x
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x
local notation3 (prettyPrint := false) "Q" => (E).presheaf.stalk q
local notation3 (prettyPrint := false) "F" => correspondenceRemainingFiniteTorSheaf f g h i z w v x
local notation3 (prettyPrint := false) "M" => correspondenceRemainingFiniteTorModule f g h i z w v x

/-- The actual affine prime localization is the actual model stalk as a B-algebra. -/
def correspondenceRemainingFiniteStalkAlgEquiv :
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    letI : Algebra B Q := ((E).presheaf.germ ⊤ q trivial).hom.toAlgebra
    Localization.AtPrime p.asIdeal ≃ₐ[B] Q := by
  letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
  letI : Algebra B Q := ((E).presheaf.germ ⊤ q trivial).hom.toAlgebra
  letI : IsLocalization.AtPrime Q p.asIdeal :=
    (isAffineOpen_top E).isLocalization_stalk ⟨q, trivial⟩
  exact IsLocalization.algEquiv p.asIdeal.primeCompl _ _

/-- Scalar transport is precisely the original section germ. -/
theorem correspondenceRemainingFiniteStalkAlgEquiv_algebraMap (b : B) :
    let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q
      (algebraMap B (Localization.AtPrime p.asIdeal) b) =
        ((E).presheaf.germ ⊤ q trivial) b := by
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  exact (correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q).commutes b

/-- The actual Tor coefficient localization and its actual stalk are linearly isomorphic
for the native localized coordinate ring, using its canonical action through the germ. -/
def correspondenceRemainingFiniteTorStalkLinearEquiv (n : ℕ) :
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    let e := correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q
    letI := stalkModule (F n) q
    letI : Module (Localization.AtPrime p.asIdeal) ((F n).presheaf.stalk q) :=
      Module.compHom _ e.toRingEquiv.toRingHom
    LocalizedModule p.asIdeal.primeCompl (M n) ≃ₗ[Localization.AtPrime p.asIdeal]
      ((F n).presheaf.stalk q) := by
  letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  letI := (isQuasicoherent_isFiniteType_correspondenceRemainingFiniteTorSheaf
    f g h i z w v x n).1
  let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
  letI := stalkModule (F n) q
  letI := sectionsStalkModule (F n) (show q ∈ (⊤ : E.Opens) from trivial)
  letI : Algebra B Q := ((E).presheaf.germ ⊤ q trivial).hom.toAlgebra
  letI : IsLocalization.AtPrime Q p.asIdeal :=
    (isAffineOpen_top E).isLocalization_stalk ⟨q, trivial⟩
  let e := correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q
  letI : Module (Localization.AtPrime p.asIdeal) ((F n).presheaf.stalk q) :=
    Module.compHom _ e.toRingEquiv.toRingHom
  letI : IsScalarTower B (Localization.AtPrime p.asIdeal) ((F n).presheaf.stalk q) :=
    IsScalarTower.of_algebraMap_smul fun b m => by
      change e (algebraMap B (Localization.AtPrime p.asIdeal) b) • m = _
      rw [correspondenceRemainingFiniteStalkAlgEquiv_algebraMap]
      rfl
  letI := isLocalizedModule_germₗ (F n) (isAffineOpen_top E)
    (show q ∈ (⊤ : E.Opens) from trivial)
  exact (IsLocalizedModule.iso p.asIdeal.primeCompl (germₗ (F n) trivial))
    .extendScalarsOfIsLocalization p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)

/-- A section divided by one goes to its actual sheaf germ. -/
theorem correspondenceRemainingFiniteTorStalkLinearEquiv_mk_one (n : ℕ) (m : M n) :
    correspondenceRemainingFiniteTorStalkLinearEquiv f g h i z w v hz hw x q n
      (LocalizedModule.mk m 1) = (F n).presheaf.germ ⊤ q trivial m := by
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  let := (isQuasicoherent_isFiniteType_correspondenceRemainingFiniteTorSheaf
    f g h i z w v x n).1
  exact IsLocalizedModule.iso_mk_one _ _ m

/-- Coefficient localization identifies the actual remaining Koszul complexes, over the
same localized coordinate ring and with the same ordered equations. -/
def correspondenceRemainingFiniteTorKoszulStalkIso (n : ℕ) {r : ℕ}
    (s : Fin r → B) :
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    let e := correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q
    letI := stalkModule (F n) q
    letI : Module (Localization.AtPrime p.asIdeal) ((F n).presheaf.stalk q) :=
      Module.compHom _ e.toRingEquiv.toRingHom
    Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (ModuleCat.of _ (LocalizedModule p.asIdeal.primeCompl (M n))) ≅
      Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (ModuleCat.of _ ((F n).presheaf.stalk q)) := by
  letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  exact (Koszul.seqComplexTensorFunctor _).mapIso
    (correspondenceRemainingFiniteTorStalkLinearEquiv f g h i z w v hz hw x q n).toModuleIso


/-- The tensor localization used by native finite pushforward is the same actual
Tor sheaf stalk, with its genuine localized-coordinate action. -/
def correspondenceRemainingFiniteTorTensorStalkLinearEquiv (n : ℕ) :
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    let e := correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q
    letI := stalkModule (F n) q
    letI : Module (Localization.AtPrime p.asIdeal) ((F n).presheaf.stalk q) :=
      Module.compHom _ e.toRingEquiv.toRingHom
    (Localization.AtPrime p.asIdeal ⊗[B] M n) ≃ₗ[Localization.AtPrime p.asIdeal]
      ((F n).presheaf.stalk q) := by
  letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
  exact (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (M n)).symm.trans
    (correspondenceRemainingFiniteTorStalkLinearEquiv f g h i z w v hz hw x q n)

/-- A pure tensor with one is the actual original section germ. -/
theorem correspondenceRemainingFiniteTorTensorStalkLinearEquiv_one_tmul
    (n : ℕ) (m : M n) :
    correspondenceRemainingFiniteTorTensorStalkLinearEquiv f g h i z w v hz hw x q n
      (1 ⊗ₜ[B] m) = (F n).presheaf.germ ⊤ q trivial m := by
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  simp only [correspondenceRemainingFiniteTorTensorStalkLinearEquiv,
    LinearEquiv.trans_apply, LocalizedModule.equivTensorProduct_symm_apply_tmul_one,
    correspondenceRemainingFiniteTorStalkLinearEquiv_mk_one]

/-- Native finite-pushforward tensor coefficients and actual sheaf stalks give
isomorphic remaining Koszul complexes with the literal same ordered equations. -/
def correspondenceRemainingFiniteTorTensorKoszulStalkIso (n : ℕ) {r : ℕ}
    (s : Fin r → B) :
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    let e := correspondenceRemainingFiniteStalkAlgEquiv f g h i z w v hz hw x q
    letI := stalkModule (F n) q
    letI : Module (Localization.AtPrime p.asIdeal) ((F n).presheaf.stalk q) :=
      Module.compHom _ e.toRingEquiv.toRingHom
    Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (ModuleCat.of _ (Localization.AtPrime p.asIdeal ⊗[B] M n)) ≅
      Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (ModuleCat.of _ ((F n).presheaf.stalk q)) := by
  letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  exact (Koszul.seqComplexTensorFunctor _).mapIso
    (correspondenceRemainingFiniteTorTensorStalkLinearEquiv
      f g h i z w v hz hw x q n).toModuleIso

end Stacks.Chow
