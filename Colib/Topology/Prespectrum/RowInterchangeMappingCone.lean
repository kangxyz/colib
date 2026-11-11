/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.MappingCone

/-!
# Actual row interchanges on finite mapping cones

The prescribed interchanges on the source and target of an actual map descend to its original
quotient cone. Inclusion, cone height, point, two-structure identity and strict arrow-map
naturality are retained. A descent map uses the full specified nullhomotopy square; its
compatibility is not inferred from its endpoint squares.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowInterchange
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  (hf : ∀ k x, qF k (f.map (k + 3) x) = f.map (k + 3) (qE k x))

/-- The original quotient cone carries the two prescribed row interchanges. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeMappingCone.lean:32-36"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
def cone (k : ℕ) : C((mappingCone f).space (k + 3), (mappingCone f).space (k + 3)) :=
  ReducedMappingCone.map _ _ (f.map (k + 3)) _ _ (f.map (k + 3))
    (qE k) (qF k) (hE k) (hF k) (hf k)

/-- The original inclusion keeps its specified target interchange. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeMappingCone.lean:37-41"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_inclusion (k : ℕ) (y : F.space (k + 3)) :
    cone f qE qF hE hF hf k ((mappingConeInclusion f).map (k + 3) y) =
      (mappingConeInclusion f).map (k + 3) (qF k y) := rfl

/-- The entire cone cylinder retains the original height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeMappingCone.lean:42-46"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_cylinder (k : ℕ) (t : unitInterval) (x : E.space (k + 3)) :
    cone f qE qF hE hF hf k ((mappingConeHomotopy f).level (k + 3) (t, x)) =
      (mappingConeHomotopy f).level (k + 3) (t, qE k x) := rfl

/-- The prescribed quotient point is unchanged. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeMappingCone.lean:47-51"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_point (k : ℕ) :
    cone f qE qF hE hF hf k ((mappingCone f).point (k + 3)) =
      (mappingCone f).point (k + 3) := ReducedMappingCone.map_point ..

/-- Actual vertex involutions give an involution on the whole quotient cone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeMappingCone.lean:52-62"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_involutive (k : ℕ) (hiE : Function.Involutive (qE k))
    (hiF : Function.Involutive (qF k)) :
    Function.Involutive (cone f qE qF hE hF hf k) := by
  intro x
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y => exact congrArg ((mappingConeInclusion f).map (k + 3)) (hiF y)
    | inr z =>
      exact congrArg (fun y => (mappingConeHomotopy f).level (k + 3) (z.1, y)) (hiE z.2)

/-- The actual two-structure equations descend on both original cone cells. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeMappingCone.lean:63-88"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_structure
    (hsE : ∀ k (x : E.space (k + 1)) (s t : unitInterval),
      qE k (E.structureMap (k + 2) (E.structureMap (k + 1) x s) t) =
        E.structureMap (k + 2) (E.structureMap (k + 1) x t) s)
    (hsF : ∀ k (x : F.space (k + 1)) (s t : unitInterval),
      qF k (F.structureMap (k + 2) (F.structureMap (k + 1) x s) t) =
        F.structureMap (k + 2) (F.structureMap (k + 1) x t) s)
    (k : ℕ) (x : (mappingCone f).space (k + 1)) (s t : unitInterval) :
    cone f qE qF hE hF hf k ((mappingCone f).structureMap (k + 2)
      ((mappingCone f).structureMap (k + 1) x s) t) =
        (mappingCone f).structureMap (k + 2)
          ((mappingCone f).structureMap (k + 1) x t) s := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y => exact congrArg ((mappingConeInclusion f).map (k + 3)) (hsF k y s t)
    | inr z =>
      exact congrArg (fun y => (mappingConeHomotopy f).level (k + 3) (z.1, y)) (hsE k z.2 s t)

variable {E' F' : LoopPrespectrum.{u}} (f' : E' ⟶ F')
  (qE' : ∀ k, C(E'.space (k + 3), E'.space (k + 3)))
  (qF' : ∀ k, C(F'.space (k + 3), F'.space (k + 3)))
  (hE' : ∀ k, qE' k (E'.point (k + 3)) = E'.point (k + 3))
  (hF' : ∀ k, qF' k (F'.point (k + 3)) = F'.point (k + 3))
  (hf' : ∀ k x, qF' k (f'.map (k + 3) x) = f'.map (k + 3) (qE' k x))

/-- A genuine strict arrow square descends with the original cellwise row squares. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeMappingCone.lean:89-105"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_map (sq : Arrow.mk f ⟶ Arrow.mk f')
    (ha : ∀ k x, qE' k (sq.left.map (k + 3) x) = sq.left.map (k + 3) (qE k x))
    (hb : ∀ k x, qF' k (sq.right.map (k + 3) x) = sq.right.map (k + 3) (qF k x))
    (k : ℕ) (x : (mappingCone f).space (k + 3)) :
    cone f' qE' qF' hE' hF' hf' k ((mappingConeMap sq).map (k + 3) x) =
      (mappingConeMap sq).map (k + 3) (cone f qE qF hE hF hf k x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y => exact congrArg ((mappingConeInclusion f').map (k + 3)) (hb k y)
    | inr z =>
      exact congrArg (fun y => (mappingConeHomotopy f').level (k + 3) (z.1, y)) (ha k z.2)

variable {G : LoopPrespectrum.{u}} (g : F ⟶ G)
  (H : Homotopy (f ≫ g) (zeroHom E G))
  (qG : ∀ k, C(G.space (k + 3), G.space (k + 3)))

/-- Actual descent requires the specified whole null square, with no replacement filler. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeMappingCone.lean:106-117"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem cone_desc
    (hg : ∀ k x, qG k (g.map (k + 3) x) = g.map (k + 3) (qF k x))
    (hH : ∀ k t x, qG k (H.level (k + 3) (t, x)) = H.level (k + 3) (t, qE k x))
    (k : ℕ) (x : (mappingCone f).space (k + 3)) :
    qG k ((mappingConeDesc f g H).map (k + 3) x) =
      (mappingConeDesc f g H).map (k + 3) (cone f qE qF hE hF hf k x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl y => exact hg k y
    | inr z => exact hH k z.1 z.2

end Topology.LoopPrespectrum.RowInterchange
