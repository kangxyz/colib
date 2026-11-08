/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteResidueTransport

/-!
# Literal remaining finite-algebra residue-degree regressions

The base is arbitrary. The source point and its actual germ prime are unchanged.
No reducedness, perfectness, smoothness, genericity, or flatness of the finite
map is needed for the pointwise comparison. Source-only pending parent checking.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceLeftImageIncidence f g h i z w v)

local notation "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation "B" => correspondenceRemainingFiniteRing f g h i z w v x
local notation "T" => correspondenceRemainingFiniteModel f g h i z w v x
local notation "π" => correspondenceRemainingFiniteModelStructure f g h i z w v x
local notation "ρ" => correspondenceRemainingFiniteModelProjection f g h i z w v x
local notation "F" => correspondenceLeftIntermediateImageMap f g h i z w v

example (q : T) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    (Ideal.comap (T.presheaf.germ ⊤ q trivial).hom
      (IsLocalRing.maximalIdeal (T.presheaf.stalk q))).comap (algebraMap R B) =
        (π q).asIdeal :=
  correspondenceRemainingFiniteGermPrime_comap_algebraMap f g h i z w v x q

example [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (q : T) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree (algebraMap R B)
      ((Ideal.comap (T.presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal (T.presheaf.stalk q))).comap (algebraMap R B))
      (Ideal.comap (T.presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal (T.presheaf.stalk q))) = F.residueDegree (ρ q) :=
  primeResidueDegree_correspondenceRemainingFiniteAlgebra f g h i z w v hz hw x q

example [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (q : T) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree (algebraMap R B) (π q).asIdeal
      (Ideal.comap (T.presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal (T.presheaf.stalk q))) = F.residueDegree (ρ q) :=
  primeResidueDegree_correspondenceRemainingFiniteAlgebra_at_imagePoint
    f g h i z w v hz hw x q

example [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (q : T) (n : ℤ) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    n * (Stacks.Length.primeResidueDegree (algebraMap R B)
      ((Ideal.comap (T.presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal (T.presheaf.stalk q))).comap (algebraMap R B))
      (Ideal.comap (T.presheaf.germ ⊤ q trivial).hom
        (IsLocalRing.maximalIdeal (T.presheaf.stalk q))) : ℤ) =
          n * (F.residueDegree (ρ q) : ℤ) := by
  letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
  exact congrArg (fun d : ℕ => n * (d : ℤ))
    (primeResidueDegree_correspondenceRemainingFiniteAlgebra f g h i z w v hz hw x q)

example [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (q : genericPoints T) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree (algebraMap R B)
      ((Ideal.comap (T.presheaf.germ ⊤ q.1 trivial).hom
        (IsLocalRing.maximalIdeal (T.presheaf.stalk q.1))).comap (algebraMap R B))
      (Ideal.comap (T.presheaf.germ ⊤ q.1 trivial).hom
        (IsLocalRing.maximalIdeal (T.presheaf.stalk q.1))) = F.residueDegree (ρ q.1) :=
  primeResidueDegree_correspondenceRemainingFiniteAlgebra f g h i z w v hz hw x q.1
