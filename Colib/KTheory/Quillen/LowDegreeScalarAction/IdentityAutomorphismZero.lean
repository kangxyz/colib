/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Quillen.LowDegreeScalarAction.IdentityAutomorphism
public import Colib.KTheory.Quillen.LowDegreeScalarAction.ExactNaturality
public import Colib.KTheory.Quillen.SpaceAction
public import Colib.Topology.Homotopy.HomotopyGroup.SelfTrackOperationZero

/-!
# The original degree-zero identity-automorphism operation

The whole normalized Q-track supplies the original K0-to-K1 operation. Its
source group law follows from actual trivial loop action on the native Q-space.
The actual composition prism supplies its natural-automorphism group law.

Implementation provenance: `Quillen/KTheory/LowDegreeScalarAction/IdentityAutomorphism.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open Topology CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
namespace CategoryTheory.ExactCategory.IdentityAutomorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)
/-- Actual degree-(0,1) operation on the original quotient. Its proved
source group law is bundled below as kZeroActionHom. -/
def kZeroAction (u : 𝟭 C ≅ 𝟭 C) : E.K 0 → E.K 1 :=
  IdentityTrack.operation (homotopy E u).toHomotopy (homotopy_fixed E u) 0

/-- The original zero input gives the identity output. -/
@[simp] theorem kZeroAction_one (u : 𝟭 C ≅ 𝟭 C) : kZeroAction E u 1 = 1 :=
  IdentityTrack.operation_one (homotopy E u).toHomotopy (homotopy_fixed E u) 0

/-- Source additivity in K-zero uses the proved actual object-loop action. -/
theorem kZeroAction_mul (u : 𝟭 C ≅ 𝟭 C) (a b : E.K 0) :
    kZeroAction E u (a * b) = kZeroAction E u a * kZeroAction E u b :=
  IdentityTrack.operation_mul_zero (homotopy E u).toHomotopy (homotopy_fixed E u)
    (qSpace_piTwo_pathTransport_loop E) a b

/-- The original degree-(0,1) operation, now equipped with its proved source group law. -/
def kZeroActionHom (u : 𝟭 C ≅ 𝟭 C) : E.K 0 →* E.K 1 where
  toFun := kZeroAction E u
  map_one' := kZeroAction_one E u
  map_mul' := kZeroAction_mul E u

/-- The actual K-zero input cube gives the unchanged track-first output cube. -/
theorem kZeroAction_cube (u : 𝟭 C ≅ 𝟭 C)
    (p : GenLoop (Fin 1) E.KSpace E.kBasepoint) :
    kZeroAction E u ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 0 p
        (IdentityTrack.track (homotopy E u).toHomotopy (homotopy_fixed E u) 0 p)⟧ : E.K 1) :=
  (genLoopNormalizedSelfTrackCube_class 0 p _).symm


end CategoryTheory.ExactCategory.IdentityAutomorphism

namespace CategoryTheory.ExactCategory.IdentityAutomorphism
variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- Exact-functor naturality retains the original degree-zero self-track operation. -/
theorem kZeroAction_natural (F : ExactFunctor EC ED)
    (u : 𝟭 C ≅ 𝟭 C) (v : 𝟭 D ≅ 𝟭 D)
    (h : ∀ A, F.toFunctor.map (u.hom.app A) = v.hom.app (F.toFunctor.obj A))
    (a : EC.K 0) : F.KMap 1 (kZeroAction EC u a) = kZeroAction ED v (F.KMap 0 a) :=
  operation_natural F u v h 0 a

/-- Additivity of the degree-zero operation in the actual natural automorphism. -/
def kZeroNatAut (E : ExactStructure C) (a : E.K 0) : Aut (𝟭 C) →* E.K 1 where
  toFun u := kZeroAction E u.asIso a
  map_one' := action_one E 0 a
  map_mul' u v := action_mul E u v 0 a
end CategoryTheory.ExactCategory.IdentityAutomorphism

attribute [colib_ref "quillen"
  "Quillen/KTheory/LowDegreeScalarAction/IdentityAutomorphism.lean:76-135,230-236"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  CategoryTheory.ExactCategory.IdentityAutomorphism.kZeroAction
  CategoryTheory.ExactCategory.IdentityAutomorphism.kZeroAction_one
  CategoryTheory.ExactCategory.IdentityAutomorphism.kZeroAction_mul
  CategoryTheory.ExactCategory.IdentityAutomorphism.kZeroActionHom
  CategoryTheory.ExactCategory.IdentityAutomorphism.kZeroAction_cube
  CategoryTheory.ExactCategory.IdentityAutomorphism.kZeroNatAut

attribute [colib_ref "quillen"
  "Quillen/KTheory/LowDegreeScalarAction/ExactNaturality.lean:175-183"
  "adaptation" "Naturality of the original degree-zero self-track through the actual exact K-map"]
  CategoryTheory.ExactCategory.IdentityAutomorphism.kZeroAction_natural
