/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorModule
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import Colib.RingTheory.Koszul.CoefficientFunctor
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Actual right Tor section localization, with its actual scalar map

Native affine germ localization identifies the tensor localization of the actual Γ Tor
module with its actual sheaf stalk. The scalar-ring isomorphism is the native affine
localization isomorphism and sends each original section to its germ. Consequently the
same ordered remaining list gives isomorphic coefficient Koszul complexes. No length,
comparison, chosen component, or flatness of the finite map is supplied by the caller.

References: native `isLocalizedModule_germₗ`, Mathlib `IsLocalizedModule.iso`, and
`LinearEquiv.extendScalarsOfIsLocalization`. This is the right instance of affine localization,
not a transport along an inadmissible reversed finite correspondence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual right affine prime localization is the actual finite-model stalk. -/
def correspondenceRightRemainingFiniteStalkAlgEquiv
    [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let Q := E.presheaf.stalk q
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    letI : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
    Localization.AtPrime p.asIdeal ≃ₐ[B] Q := by
  dsimp only
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let Q := E.presheaf.stalk q
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
  let : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
  let : IsLocalization.AtPrime Q p.asIdeal :=
    (isAffineOpen_top E).isLocalization_stalk ⟨q, trivial⟩
  exact IsLocalization.algEquiv p.asIdeal.primeCompl _ _

/-- The localization-to-stalk map is precisely the original section germ on scalars. -/
theorem correspondenceRightRemainingFiniteStalkAlgEquiv_algebraMap
    [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (b : correspondenceRightRemainingFiniteRing f g h i z w v x) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let Q := E.presheaf.stalk q
    let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    let : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
    correspondenceRightRemainingFiniteStalkAlgEquiv f g h i z w v hw hv x q
      (algebraMap B (Localization.AtPrime p.asIdeal) b) = E.presheaf.germ ⊤ q trivial b := by
  dsimp only
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let Q := E.presheaf.stalk q
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
  exact (correspondenceRightRemainingFiniteStalkAlgEquiv f g h i z w v hw hv x q).commutes b

/-- The actual tensor-localized Γ coefficient has its original sheaf-stalk action. -/
def correspondenceRightRemainingFiniteTorTensorStalkLinearEquiv
    [IsSeparated h] [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) (n : ℕ) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let Q := E.presheaf.stalk q
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x n
    letI : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
    let e := correspondenceRightRemainingFiniteStalkAlgEquiv f g h i z w v hw hv x q
    letI := stalkModule F q
    letI : Module (Localization.AtPrime p.asIdeal) (F.presheaf.stalk q) :=
      Module.compHom _ e.toRingEquiv.toRingHom
    (Localization.AtPrime p.asIdeal ⊗[B] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      (F.presheaf.stalk q) := by
  dsimp only
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let Q := E.presheaf.stalk q
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
  let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x n
  let := (isQuasicoherent_isFiniteType_correspondenceRightRemainingFiniteTorSheaf
    f g h i z w v x n).1
  let := stalkModule F q
  let := sectionsStalkModule F (show q ∈ (⊤ : E.Opens) from trivial)
  let : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
  let : IsLocalization.AtPrime Q p.asIdeal :=
    (isAffineOpen_top E).isLocalization_stalk ⟨q, trivial⟩
  let e := correspondenceRightRemainingFiniteStalkAlgEquiv f g h i z w v hw hv x q
  let : Module (Localization.AtPrime p.asIdeal) (F.presheaf.stalk q) :=
    Module.compHom _ e.toRingEquiv.toRingHom
  let : IsScalarTower B (Localization.AtPrime p.asIdeal) (F.presheaf.stalk q) :=
    IsScalarTower.of_algebraMap_smul fun b m => by
      change e (algebraMap B (Localization.AtPrime p.asIdeal) b) • m = _
      rw [correspondenceRightRemainingFiniteStalkAlgEquiv_algebraMap]
      rfl
  let := isLocalizedModule_germₗ F (isAffineOpen_top E)
    (show q ∈ (⊤ : E.Opens) from trivial)
  exact (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).symm.trans
    (LinearEquiv.extendScalarsOfIsLocalization p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)
      (IsLocalizedModule.iso p.asIdeal.primeCompl
        (germₗ F (show q ∈ (⊤ : E.Opens) from trivial))))

/-- The coefficient comparison preserves the same ordered Koszul equations and all degrees. -/
def correspondenceRightRemainingFiniteTorTensorKoszulStalkIso
    [IsSeparated h] [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) (n : ℕ) {r : ℕ}
    (s : Fin r → correspondenceRightRemainingFiniteRing f g h i z w v x) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let Q := E.presheaf.stalk q
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x n
    letI : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
    let e := correspondenceRightRemainingFiniteStalkAlgEquiv f g h i z w v hw hv x q
    letI := stalkModule F q
    letI : Module (Localization.AtPrime p.asIdeal) (F.presheaf.stalk q) :=
      Module.compHom _ e.toRingEquiv.toRingHom
    Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[B] M)) ≅
      Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (ModuleCat.of (Localization.AtPrime p.asIdeal) (F.presheaf.stalk q)) := by
  dsimp only
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let Q := E.presheaf.stalk q
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let : Algebra B Q := (E.presheaf.germ ⊤ q trivial).hom.toAlgebra
  let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
  let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n
  let e := correspondenceRightRemainingFiniteStalkAlgEquiv f g h i z w v hw hv x q
  let := stalkModule F q
  let : Module (Localization.AtPrime p.asIdeal) (F.presheaf.stalk q) :=
    Module.compHom _ e.toRingEquiv.toRingHom
  exact (Koszul.seqComplexTensorFunctor
    (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))).mapIso
    (correspondenceRightRemainingFiniteTorTensorStalkLinearEquiv
      f g h i z w v hw hv x q n).toModuleIso

end Stacks.Chow
