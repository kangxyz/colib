/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorStalkEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence Stacks.Chow Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

variable [IsSeparated g] [IsSeparated h]
  [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

example
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (n : ℕ) {r : ℕ} (s : Fin r → (correspondenceRemainingFiniteRing f g h i z w v x)) (a : ℕ) :
    let E := correspondenceRemainingFiniteModel f g h i z w v x
    let B := correspondenceRemainingFiniteRing f g h i z w v x
    let Q := (correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q
    let F := correspondenceRemainingFiniteTorSheaf f g h i z w v x
    let M := correspondenceRemainingFiniteTorModule f g h i z w v x
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    letI := stalkModule (F n) q
    Module.length (Localization.AtPrime p.asIdeal)
      ((Koszul.seqComplexTensor (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
        (Localization.AtPrime p.asIdeal ⊗[B] M n)).homology a) =
      Module.length Q
        ((Koszul.seqComplexTensor (fun j => (E).presheaf.germ ⊤ q trivial (s j))
          ((F n).presheaf.stalk q)).homology a) :=
  length_correspondenceRemainingFiniteTorTensorKoszul_eq_stalk f g h i z w v hz hw x q n s a

example
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (n : ℕ) {r : ℕ} (s : Fin r → (correspondenceRemainingFiniteRing f g h i z w v x)) :
    let E := correspondenceRemainingFiniteModel f g h i z w v x
    let B := correspondenceRemainingFiniteRing f g h i z w v x
    let Q := (correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q
    let F := correspondenceRemainingFiniteTorSheaf f g h i z w v x
    let M := correspondenceRemainingFiniteTorModule f g h i z w v x
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    let p := (isAffineOpen_top E).primeIdealOf ⟨q, trivial⟩
    letI := stalkModule (F n) q
    Koszul.seqEuler (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (s j))
      (Localization.AtPrime p.asIdeal ⊗[B] M n) =
      Koszul.seqEuler (fun j => (E).presheaf.germ ⊤ q trivial (s j))
        ((F n).presheaf.stalk q) :=
  seqEuler_correspondenceRemainingFiniteTorTensor_eq_stalk f g h i z w v hz hw x q n s
