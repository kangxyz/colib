/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.MappingCone

/-!
# Homotopies of mapping-cone maps from moving strict squares

Two actual homotopies between the sides of strict arrow squares induce a whole coherent
homotopy between the existing mapping-cone maps, provided the sides form a strictly commuting
square at every time. The independent homotopy parameter is curried into the compact-open
interval mapping space before quotient descent. Thus the construction does not require a
product to preserve a quotient, or a local compactness assumption on prespectrum levels.

The target formula is the moving right side followed by the original cone inclusion; the
cylinder formula moves the left side while preserving the original cone coordinate. Every
structure equation retains both the homotopy parameter and the loop parameter independently.
-/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

variable {A B : Arrow LoopPrespectrum.{u}} {s t : A ⟶ B}
  (L : Homotopy s.left t.left) (M : Homotopy s.right t.right)
  (h : ∀ n r x, M.level n (r, A.hom.map n x) = B.hom.map n (L.level n (r, x)))

/-- Move both sides of the square and descend into the interval mapping space before evaluation.
The original cone coordinate remains independent of the moving-square parameter. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeMapHomotopy.lean:39-71"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def mappingConeMapHomotopyFamily (n : ℕ) :
    C((mappingCone A.hom).space n, C(unitInterval, (mappingCone B.hom).space n)) :=
  ReducedMappingCone.desc (A.left.point n) (A.right.point n) (A.hom.map n)
    (ContinuousMap.curry ⟨fun z : A.right.space n × unitInterval ↦
      (mappingConeInclusion B.hom).map n (M.level n (z.2, z.1)), by fun_prop⟩)
    (ContinuousMap.curry ⟨fun z : (unitInterval × A.left.space n) × unitInterval ↦
      ReducedMappingCone.cylinder (B.left.point n) (B.right.point n) (B.hom.map n)
        (z.1.1, L.level n (z.2, z.1.2)),
      (ReducedMappingCone.cylinder (B.left.point n) (B.right.point n)
        (B.hom.map n)).continuous.comp (by fun_prop)⟩)
    (by
      intro x
      ext r
      exact (ReducedMappingCone.cylinder_zero (B.left.point n) (B.right.point n)
        (B.hom.map n) (L.level n (r, x))).trans
          (congrArg (ReducedMappingCone.inr (B.left.point n) (B.right.point n) (B.hom.map n))
            (h n r x).symm))
    (by
      intro x
      ext r
      exact (ReducedMappingCone.cylinder_one (B.left.point n) (B.right.point n)
        (B.hom.map n) (L.level n (r, x))).trans
          (congrArg (ReducedMappingCone.inr (B.left.point n) (B.right.point n) (B.hom.map n))
            (M.at_point n r).symm))
    (by
      intro q
      ext r
      change ReducedMappingCone.cylinder (B.left.point n) (B.right.point n) (B.hom.map n)
        (q, L.level n (r, A.left.point n)) =
          ReducedMappingCone.inr (B.left.point n) (B.right.point n) (B.hom.map n)
            (M.level n (r, A.right.point n))
      rw [L.at_point, M.at_point]
      exact ReducedMappingCone.cylinder_base ..)

/-- On the original target, the interval-valued descent is precisely the moving right side. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeMapHomotopy.lean:72-77"
  "adaptation" "Original whole maps and independent time coordinates retained", simp]
theorem mappingConeMapHomotopyFamily_inclusion
    (n : ℕ) (r : unitInterval) (y : A.right.space n) :
    mappingConeMapHomotopyFamily L M h n ((mappingConeInclusion A.hom).map n y) r =
      (mappingConeInclusion B.hom).map n (M.level n (r, y)) := rfl

/-- The interval-valued descent moves the left side without changing the cone coordinate. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeMapHomotopy.lean:78-86"
  "adaptation" "Original whole maps and independent time coordinates retained", simp]
theorem mappingConeMapHomotopyFamily_cylinder
    (n : ℕ) (r q : unitInterval) (x : A.left.space n) :
    mappingConeMapHomotopyFamily L M h n
      (ReducedMappingCone.cylinder (A.left.point n) (A.right.point n) (A.hom.map n) (q, x)) r =
        ReducedMappingCone.cylinder (B.left.point n) (B.right.point n) (B.hom.map n)
          (q, L.level n (r, x)) := rfl

/-- A whole all-time commuting square of side homotopies induces a coherent based homotopy
between the existing strict mapping-cone maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeMapHomotopy.lean:87-116"
  "adaptation" "Original whole maps and independent time coordinates retained"]
def mappingConeMapHomotopy : Homotopy (mappingConeMap s) (mappingConeMap t) where
  level n := ⟨fun z ↦ mappingConeMapHomotopyFamily L M h n z.2 z.1,
    (mappingConeMapHomotopyFamily L M h n).uncurry.continuous.comp continuous_swap⟩
  at_zero n p := by
    induction p using Quot.inductionOn with
    | h z => cases z with
      | inl y =>
        exact congrArg ((mappingConeInclusion B.hom).map n) (M.at_zero n y)
      | inr z =>
        exact congrArg (fun x ↦ ReducedMappingCone.cylinder (B.left.point n) (B.right.point n)
          (B.hom.map n) (z.1, x)) (L.at_zero n z.2)
  at_one n p := by
    induction p using Quot.inductionOn with
    | h z => cases z with
      | inl y =>
        exact congrArg ((mappingConeInclusion B.hom).map n) (M.at_one n y)
      | inr z =>
        exact congrArg (fun x ↦ ReducedMappingCone.cylinder (B.left.point n) (B.right.point n)
          (B.hom.map n) (z.1, x)) (L.at_one n z.2)
  at_point n r := congrArg ((mappingConeInclusion B.hom).map n) (M.at_point n r)
  comm n r p v := by
    induction p using Quot.inductionOn with
    | h z => cases z with
      | inl y =>
        exact congrArg ((mappingConeInclusion B.hom).map (n + 1)) (M.comm n r y v)
      | inr z =>
        exact congrArg (fun x ↦ ReducedMappingCone.cylinder (B.left.point (n + 1))
          (B.right.point (n + 1)) (B.hom.map (n + 1)) (z.1, x)) (L.comm n r z.2 v)

/-- Every time on the original target is the moving right side followed by the cone inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeMapHomotopy.lean:117-122"
  "adaptation" "Original whole maps and independent time coordinates retained", simp]
theorem mappingConeMapHomotopy_inclusion
    (n : ℕ) (r : unitInterval) (y : A.right.space n) :
    (mappingConeMapHomotopy L M h).level n (r, (mappingConeInclusion A.hom).map n y) =
      (mappingConeInclusion B.hom).map n (M.level n (r, y)) := rfl

/-- Every point of the actual source cylinder retains its original cone coordinate. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeMapHomotopy.lean:123-130"
  "adaptation" "Original whole maps and independent time coordinates retained", simp]
theorem mappingConeMapHomotopy_cylinder
    (n : ℕ) (r q : unitInterval) (x : A.left.space n) :
    (mappingConeMapHomotopy L M h).level n
      (r, ReducedMappingCone.cylinder (A.left.point n) (A.right.point n) (A.hom.map n) (q, x)) =
        ReducedMappingCone.cylinder (B.left.point n) (B.right.point n) (B.hom.map n)
          (q, L.level n (r, x)) := rfl

end Topology.LoopPrespectrum
