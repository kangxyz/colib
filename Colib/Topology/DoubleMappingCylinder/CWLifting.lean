/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.HomotopyDescent
public import Colib.Topology.CWComplex.HomotopyLifting

/-!
# Actual lifting on a double cylinder of classical CW subtypes

Lift on the two original CW ends, lift the full attaching homotopy with its
prescribed endpoints on the original CW source, and descend through the literal
TopCat pushout. No CW structure or Hausdorff assumption on the pushout is used.
The only lifting hypothesis is the actual finite cubical BoundaryLifting of p.
-/
@[expose] public section

open Topology
noncomputable section
open CategoryTheory Limits MonoidalCategory Set
open scoped unitInterval
universe u
namespace TopCat.DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]
variable {D : TopCat.{u}} (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
variable {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (TopCat.intervalEndpoints (TopCat.of A)) (endMap f g) l e)
variable {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
variable (p : C(E, T)) (hp : CubicalSubdivision.BoundaryLifting p) (d : C(D, T))

/-- The original left endpoint restriction has a genuine CW lift. -/
def cwLiftLeft (a : C(B, D)) : C(B, E) := Topology.CWComplex.globalLift B p hp (d.comp a)

/-- The original right endpoint restriction has a genuine CW lift. -/
def cwLiftRight (a : C(C, D)) : C(C, E) := Topology.CWComplex.globalLift C p hp (d.comp a)

/-- The full original base cylinder, with its endpoint equalities supplied by the
strict equations of the two independently constructed CW lifts. -/
def cwLiftBaseHomotopy :
    (p.comp ((cwLiftLeft B p hp d (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e)).comp f.hom)).Homotopy
      (p.comp ((cwLiftRight C p hp d
        (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e)).comp g.hom)) :=
  ((ContinuousMap.Homotopy.refl d).comp (endpointHomotopy f g sq)).cast
    (by
      apply ContinuousMap.ext
      intro a
      exact (ContinuousMap.congr_fun
        (Topology.CWComplex.globalLift_comp B p hp (d.comp (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e))) (f a)).symm)
    (by
      apply ContinuousMap.ext
      intro a
      exact (ContinuousMap.congr_fun
        (Topology.CWComplex.globalLift_comp C p hp
          (d.comp (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e))) (g a)).symm)

/-- The exact attaching-cylinder homotopy lifts with both original end maps. -/
def cwLiftCylinderHomotopy :
    ((cwLiftLeft B p hp d (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e)).comp f.hom).Homotopy
      ((cwLiftRight C p hp d (gapRightEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e)).comp g.hom) :=
  Topology.CWComplex.homotopyLift A p hp _ _ (cwLiftBaseHomotopy A B C f g sq p hp d)

/-- Descent of the actual lifted maps and homotopy gives a continuous global lift. -/
def cwLift : C(D, E) :=
  homotopyDesc f g sq (cwLiftLeft B p hp d (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e))
    (cwLiftRight C p hp d (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e))
    (cwLiftCylinderHomotopy A B C f g sq p hp d)

/-- The global lift retains its original left CW lift pointwise. -/
theorem cwLift_left : (cwLift A B C f g sq p hp d).comp (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e) =
    cwLiftLeft B p hp d (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e) := homotopyDesc_left f g sq _ _ _

/-- The global lift retains its original right CW lift pointwise. -/
theorem cwLift_right : (cwLift A B C f g sq p hp d).comp (gapRightEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e) =
    cwLiftRight C p hp d (gapRightEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e) := homotopyDesc_right f g sq _ _ _

/-- The entire cylinder of the descended lift is the constructed lifted homotopy. -/
theorem cwLift_cylinder (t : I) (a : A) :
    cwLift A B C f g sq p hp d (l (a, ULift.up t)) =
      cwLiftCylinderHomotopy A B C f g sq p hp d (t, a) :=
  homotopyDesc_apply_cylinder f g sq _ _ _ t a

/-- The entire lifted cylinder projects to the original base cylinder. -/
theorem cwLiftCylinderHomotopy_project (t : I) (a : A) :
    p (cwLiftCylinderHomotopy A B C f g sq p hp d (t, a)) = d (l (a, ULift.up t)) :=
  Topology.CWComplex.homotopyLift_project A p hp _ _ _ t a

/-- The actual pushout universal property proves the strict global base-map equation. -/
theorem cwLift_comp : p.comp (cwLift A B C f g sq p hp d) = d := by
  have h : TopCat.ofHom (p.comp (cwLift A B C f g sq p hp d)) = TopCat.ofHom d := by
    apply sq.hom_ext
    · apply ConcreteCategory.hom_ext
      intro z
      rcases z with ⟨a, t⟩
      change p (cwLift A B C f g sq p hp d (l (a, t))) = d (l (a, t))
      exact (congrArg p (cwLift_cylinder A B C f g sq p hp d t.down a)).trans
        (cwLiftCylinderHomotopy_project A B C f g sq p hp d t.down a)
    · apply ConcreteCategory.hom_ext
      intro z
      cases z with
      | inl b =>
        change p (cwLift A B C f g sq p hp d (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e b)) = d (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e b)
        exact (congrArg p (ContinuousMap.congr_fun
          (cwLift_left A B C f g sq p hp d) b)).trans
            (ContinuousMap.congr_fun
              (Topology.CWComplex.globalLift_comp B p hp (d.comp (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e))) b)
      | inr c =>
        change p (cwLift A B C f g sq p hp d
          (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e c)) =
            d (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e c)
        exact (congrArg p (ContinuousMap.congr_fun
          (cwLift_right A B C f g sq p hp d) c)).trans
            (ContinuousMap.congr_fun
              (Topology.CWComplex.globalLift_comp C p hp
                (d.comp (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e))) c)
  exact congrArg (fun k : D ⟶ TopCat.of T ↦ k.hom) h

include A B C f g sq hp in
/-- Every original map on this actual cylinder lifts against any actual finite
boundary-lifting map; no preexisting lift or recognition certificate is assumed. -/
theorem exists_cwLift : ∃ q : C(D, E), p.comp q = d :=
  ⟨cwLift A B C f g sq p hp d, cwLift_comp A B C f g sq p hp d⟩

end TopCat.DoubleCylinder
