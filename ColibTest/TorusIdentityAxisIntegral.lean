module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusIdentityAxisIntegral

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers Stacks.Chow

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [Field k]
variable (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]

-- The actual signed identity-axis coefficient is killed by the existing quotient.
example (a : Cor.mk X ⟶ Cor.mk (base (Spec (.of k)))) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X))
        (ULift.up (structureCorrespondenceCoeff (X := X.left) X.hom a •
          torusIdentityGraph k X)) = 0 := by
  rw [← torusIdentityAxis_one_app_eq_coeff k X a]
  exact congrArg (fun η => η.hom.app (op (Cor.mk X)) (ULift.up a))
    (torusIdentityAxis_toReducedTorus k 1 0)

-- Negative multiplicity survives literally; the image is not restricted to effective cycles.
example :
    (ULift.up ((-3 : ℤ) • torusIdentityGraph k X)) ∈
      ((torusIdentityAxis k 1 0).hom.app (op (Cor.mk X))).hom.range :=
  (mem_range_torusIdentityAxis_one_iff k X _).mpr ⟨-3, rfl⟩

-- The target comparison preserves the genuine unit-one graph, not an input-object placeholder.
example :
    torusIdentityGraph k X ≫
        (Cor.graphFunctor k).map (torusPowerOneIso (Spec (.of k))).hom =
      (Cor.graphFunctor k).map (structureMorphism X ≫ torusOne (Spec (.of k))) :=
  torusIdentityGraph_powerOneIso k X

-- The inverse of coefficient extraction is the actual structure-graph cycle.
example (n : ℤ) :
    (structureCorrespondenceEquiv (X := X.left) X.hom).symm n =
      n • structureGraphCorrespondence (X := X.left) X.hom :=
  rfl
