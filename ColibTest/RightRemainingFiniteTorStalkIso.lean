/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorStalkIso

/-! Literal endpoint consumers.  -/

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

example
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
  exact correspondenceRightRemainingFiniteStalkAlgEquiv
    f g h i z w v hw hv x q

example
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
  exact correspondenceRightRemainingFiniteTorTensorStalkLinearEquiv
    f g h i z w v hw hv x q n

-- Consume the actual ordered-list comparison at every homological degree.
example
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
  exact correspondenceRightRemainingFiniteTorTensorKoszulStalkIso
    f g h i z w v hw hv x q n s

end Stacks.Chow
