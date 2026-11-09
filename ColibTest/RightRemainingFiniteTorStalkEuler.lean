/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorStalkEuler

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
  [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (n : ℕ) {r : ℕ} (s : Fin r → (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    letI := stalkModule (F n) q
    Koszul.seqEuler (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
      (Localization.AtPrime p.asIdeal ⊗[B] M n) =
      Koszul.seqEuler (fun j => (E).presheaf.germ ⊤ q trivial (s j))
        ((F n).presheaf.stalk q) := by
  exact seqEuler_correspondenceRightRemainingFiniteTorTensor_eq_stalk
    f g h i z w v hw hv x q n s

-- Consume the actual ordered-list comparison at every homological degree.
example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (n : ℕ) {r : ℕ} (s : Fin r → (correspondenceRightRemainingFiniteRing f g h i z w v x)) (a : ℕ) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let Q := (correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q
    let F := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    letI := stalkModule (F n) q
    Module.length (Localization.AtPrime p.asIdeal)
      ((Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (Localization.AtPrime p.asIdeal ⊗[B] M n)).homology a) =
      Module.length Q
        ((Koszul.seqComplexTensor (fun j => (E).presheaf.germ ⊤ q trivial (s j))
          ((F n).presheaf.stalk q)).homology a) := by
  exact length_correspondenceRightRemainingFiniteTorTensorKoszul_eq_stalk
    f g h i z w v hw hv x q n s a

end Stacks.Chow
