/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.Fibration.CofiberBoundaryTrack
import Colib.KTheory.Waldhausen.Fibration.CofiberPrismLeftPrefix
import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberComponentTranslation
import Colib.KTheory.Waldhausen.Fibration.IdentityCofiberNormalization

/-!
# Prepared regressions for the prescribed cofiber-prism boundary

These statements have not been compiled. They retain independent category universes,
comparison/boundary/loop times, the full reversed canonical-fiber path, and the specified
identity-cofiber suffix. Boundary concatenation splits boundary time; left prefix splits
loop time. The two whole stored-path equalities are stronger than endpoint checks.
No canonical-comparison weakness, fibration, cylinder or connectivity is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration CategoryTheory.Waldhausen.QuotientRows
open Topology Convexity unitInterval
open scoped Topology Simplicial
universe u v
namespace ColibTest.WaldhausenCofiberBoundary

section Boundary
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- The delivered comparison is data, with its actual two prescribed paths. -/
example :
    ((W.cofiberPrismPrefixLoopPath i q hi hwi hQ).trans
      (W.cofiberObjectLoopPath i q hi hQ)).Homotopy
      ((W.identityCofiberSuffixPath A).trans (W.weakObjectSquareLoopPath i hwi)) :=
  W.cofiberBoundaryTrack i q hi hwi hQ

/-- All three independent parameters still evaluate the original family. -/
theorem boundary_family (a s t : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (a, s) t =
      W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (a, s) t :=
  W.cofiberBoundaryTrack_apply i q hi hwi hQ a s t

/-- The full coordinatewise interpolation is the native prescribed square comparison. -/
theorem boundary_interpolation (a s t : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (a, s) t =
      W.cofiberPrismCompositionCube i q hi hwi hQ
        ((unitSquarePathHomotopy
          (((Path.refl (0 : unitInterval)).prod Path.id).trans
            (Path.id.prod (Path.refl (1 : unitInterval))))
          ((Path.id.prod (Path.refl (0 : unitInterval))).trans
            ((Path.refl (1 : unitInterval)).prod Path.id)) (a, s)).1,
          (unitSquarePathHomotopy
            (((Path.refl (0 : unitInterval)).prod Path.id).trans
              (Path.id.prod (Path.refl (1 : unitInterval))))
            ((Path.id.prod (Path.refl (0 : unitInterval))).trans
              ((Path.refl (1 : unitInterval)).prod Path.id)) (a, s)).2, t) := by
  exact (W.cofiberBoundaryTrack_apply i q hi hwi hQ a s t).trans
    (W.cofiberPrismBoundaryHomotopy_apply i q hi hwi hQ a s t)

/-- The forward boundary route splits boundary time s, with independent loop time t. -/
theorem boundary_zero_half_interval (s t : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (0, s) t =
      if h : (s : ℝ) ≤ 1 / 2 then
        W.cofiberPrismCompositionCube i q hi hwi hQ
          (0, ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩, t)
      else
        W.cofiberObjectLoopTrack i q hi hQ
          (⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩, t) := by
  rw [W.cofiberBoundaryTrack_apply]
  exact W.cofiberPrismBoundaryHomotopy_zero i q hi hwi hQ s t

/-- The other route uses the entire identity suffix followed by the actual inclusion square. -/
theorem boundary_one_half_interval (s t : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (1, s) t =
      if h : (s : ℝ) ≤ 1 / 2 then
        W.identityCofiberSuffixPath A
          ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩ t
      else
        W.weakObjectSquareTrack i hwi
          (⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩, t) := by
  rw [W.cofiberBoundaryTrack_apply]
  exact W.cofiberPrismBoundaryHomotopy_one i q hi hwi hQ s t

/-- Every comparison time fixes the literal source loop with its constant suffix. -/
theorem boundary_source (a : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (a, 0) =
      (W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint) :=
  Path.Homotopy.source _ a

/-- Every comparison time fixes the literal middle object loop. -/
theorem boundary_target (a : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (a, 1) = W.kZeroObjectLoop B :=
  Path.Homotopy.target _ a

/-- The whole comparison consists of based loops, not unbased paths. -/
theorem boundary_loop_zero (a s : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (a, s) 0 = W.kBasepoint :=
  (W.cofiberBoundaryTrack i q hi hwi hQ (a, s)).source

/-- The terminal loop time is fixed for both moving parameters independently. -/
theorem boundary_loop_one (a s : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (a, s) 1 = W.kBasepoint :=
  (W.cofiberBoundaryTrack i q hi hwi hQ (a, s)).target

/-- The prefix is the entire comparison-zero cube edge. -/
theorem prefix_apply (s t : unitInterval) :
    W.cofiberPrismPrefixLoopPath i q hi hwi hQ s t =
      W.cofiberPrismCompositionCube i q hi hwi hQ (0, s, t) := rfl

/-- The forward prefix starts at the literal constant-suffix loop. -/
theorem prefix_source :
    W.cofiberPrismPrefixLoopPath i q hi hwi hQ 0 =
      (W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint) :=
  (W.cofiberPrismPrefixLoopPath i q hi hwi hQ).source

/-- The forward prefix ends at the actual source and quotient concatenation. -/
theorem prefix_target :
    W.cofiberPrismPrefixLoopPath i q hi hwi hQ 1 =
      (W.kZeroObjectLoop A).trans (W.kZeroObjectLoop Q) :=
  (W.cofiberPrismPrefixLoopPath i q hi hwi hQ).target

/-- Currying keeps both original cofiber-triangle times. -/
theorem cofiber_path_apply (s t : unitInterval) :
    W.cofiberObjectLoopPath i q hi hQ s t = W.cofiberObjectLoopTrack i q hi hQ (s, t) := rfl

/-- The suffix is the specified identity-cofiber triangle, not a chosen right-unit path. -/
theorem suffix_apply (s t : unitInterval) :
    W.identityCofiberSuffixPath A s t =
      W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) (s, t) :=
  W.identityCofiberSuffixPath_apply A s t

/-- The curried inclusion square retains both nerve time and object-loop time. -/
theorem inclusion_path_apply (s t : unitInterval) :
    W.weakObjectSquareLoopPath i hwi s t = W.weakObjectSquareTrack i hwi (s, t) := rfl

end Boundary

section CanonicalFiber
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {V : Structure C}
  (N : NestedWeakEquivalences V) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : N.coarse.cof i) (hwi : N.coarse.weq i)
  (hQ : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

/-- Gluing certifies the actual displayed quotient, not an equivalent replacement. -/
theorem acyclic_quotient_object :
    (cofiberPrismAcyclicQuotient N i q hi hwi hQ).obj = Q := rfl

/-- The stored canonical coordinate is the full original transformation with only s reversed. -/
theorem fiber_transformation (t s : unitInterval) :
    (canonicalFiberObjectLoop N (cofiberPrismAcyclicQuotient N i q hi hwi hQ) t).val.2 s =
      acyclicObjectTransformationTrack N (cofiberPrismAcyclicQuotient N i q hi hwi hQ)
        (unitInterval.symm s, t) :=
  canonicalFiberObjectLoop_path_transformation N _ t s

/-- The complete quotient S-face agrees with that original reversed fiber path. -/
theorem quotient_face (t s : unitInterval) :
    N.coarse.cofiberPrismRealization i q hi hwi hQ
        ((StdSimplex.homeomorphI.symm t).map (SimplexCategory.δ 0), unitInterval.symm s) =
      (canonicalFiberObjectLoop N (cofiberPrismAcyclicQuotient N i q hi hwi hQ) t).val.2 s :=
  cofiberPrismRealization_quotient_fiber N i q hi hwi hQ t s

/-- Prefix concatenation splits loop time t, while reversed fiber time s is independent. -/
theorem prefix_loop_half_interval (t s : unitInterval) :
    N.coarse.cofiberPrismCompositionCube i q hi hwi hQ (0, unitInterval.symm s, t) =
      if h : (t : ℝ) ≤ 1 / 2 then
        N.coarse.kZeroObjectLoop A
          ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else
        (canonicalFiberObjectLoop N (cofiberPrismAcyclicQuotient N i q hi hwi hQ)
          ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩).val.2 s :=
  cofiberPrismCompositionCube_zero_fiber N i q hi hwi hQ t s

/-- The whole stored prefixed path is exactly the reversed original prism prefix. -/
theorem prefixed_path_eq_reversed_prefix :
    (canonicalFiberObjectPrefixed N A (cofiberPrismAcyclicQuotient N i q hi hwi hQ)).val.2 =
      (N.coarse.cofiberPrismPrefixLoopPath i q hi hwi hQ).symm.toContinuousMap := by
  apply ContinuousMap.ext
  intro s
  apply Path.ext
  funext t
  change loopLeftTranslationEquiv (N.coarse.kZeroObjectLoop A)
      ((canonicalFiberObjectLoopTranspose N
        (cofiberPrismAcyclicQuotient N i q hi hwi hQ)).val.2 s) t =
    N.coarse.cofiberPrismCompositionCube i q hi hwi hQ (0, unitInterval.symm s, t)
  exact cofiberPrismCompositionCube_zero_leftPrefix N i q hi hwi hQ s t

/-- Actual suffix transport appends E to the entire reversed P, with its full parametrization. -/
theorem transported_path_eq_reversed_prefix_suffix :
    (canonicalFiberObjectPrefixTransport N A
      (cofiberPrismAcyclicQuotient N i q hi hwi hQ)).val.2 =
      ((N.coarse.cofiberPrismPrefixLoopPath i q hi hwi hQ).symm.trans
        (N.coarse.identityCofiberSuffixPath A)).toContinuousMap := by
  rw [canonicalFiberObjectPrefixTransport_path]
  apply ContinuousMap.ext
  intro s
  apply Path.ext
  funext t
  change ((HomotopyFiber.toPath
      (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      ((N.coarse.kZeroObjectLoop A).trans (Path.refl N.coarse.kBasepoint))
      (canonicalFiberObjectPrefixed N A (cofiberPrismAcyclicQuotient N i q hi hwi hQ))).trans
        (N.coarse.identityCofiberSuffixPath A) s) t =
    ((N.coarse.cofiberPrismPrefixLoopPath i q hi hwi hQ).symm.trans
      (N.coarse.identityCofiberSuffixPath A) s) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with h
  · exact congrArg (fun p : C(unitInterval, Path N.coarse.kBasepoint N.coarse.kBasepoint) =>
      p ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩ t)
      (prefixed_path_eq_reversed_prefix N i q hi hwi hQ)
  · rfl

/-- The genuine component equivalence carries the original point to precisely P.symm.trans E. -/
theorem component_path_eq_reversed_prefix_suffix :
    (canonicalFiberComponentEquiv N A
      (canonicalFiberObjectLoopTranspose N
        (cofiberPrismAcyclicQuotient N i q hi hwi hQ))).val.2 =
      ((N.coarse.cofiberPrismPrefixLoopPath i q hi hwi hQ).symm.trans
        (N.coarse.identityCofiberSuffixPath A)).toContinuousMap := by
  rw [canonicalFiberComponentEquiv_object]
  exact transported_path_eq_reversed_prefix_suffix N i q hi hwi hQ

/-- The actual translated point retains its unchanged fine source coordinate. -/
theorem component_source :
    (canonicalFiberComponentEquiv N A
      (canonicalFiberObjectLoopTranspose N
        (cofiberPrismAcyclicQuotient N i q hi hwi hQ))).val.1 =
      (V.kZeroObjectLoop A).trans (V.kZeroObjectLoop Q) := by
  simpa only [canonicalFiberComponentEquiv_object] using
    (canonicalFiberObjectPrefixTransport_source N A (cofiberPrismAcyclicQuotient N i q hi hwi hQ))

end CanonicalFiber

section Normalization
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (W : Structure C) (A : C)

/-- The general n-equivalence keeps the actual suffix, independently of degree-one comparison. -/
theorem component_equiv_definition (n : ℕ) :
    W.identityCofiberComponentEquiv A n =
      (loopLeftTranslationHomotopyEquiv (W.kZeroObjectLoop A) n).trans
        (pathTransport (W.identityCofiberSuffixPath A) n) := rfl

/-- Normalization compares the induced degree-one maps, without identifying the paths. -/
theorem suffix_degree_one
    (b : HomotopyGroup.Pi 1 (Path W.kBasepoint W.kBasepoint)
      ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint))) :
    pathTransport (W.identityCofiberSuffixPath A) 1 b =
      pathTransport (loopRightUnitPath (W.kZeroObjectLoop A)) 1 b :=
  W.identityCofiberSuffixPath_transport_eq A b

/-- This is only the specified degree-one equivalence comparison, with no Laurent sign claim. -/
theorem component_degree_one :
    W.identityCofiberComponentEquiv A 1 =
      loopLeftComponentHomotopyEquiv (W.kZeroObjectLoop A) 1 :=
  W.identityCofiberComponentEquiv_eq A

end Normalization
end ColibTest.WaldhausenCofiberBoundary
