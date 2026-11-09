/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.DoubleMappingCylinder.BaseLineHEP
public import Colib.Topology.HomotopyPullback.Pushout
public import Colib.Topology.Pushout.HomotopyEquivalence

/-!
# Reduction of the original homotopy-pushout levels

The actual reduced homotopy-pushout quotient is the pushout collapsing the literal chosen-point
interval in the ordinary double mapping cylinder. HEP of the original three point inclusions
makes this exact reduction a homotopy equivalence and proves HEP of the resulting original point.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/PushoutReduction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout

variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C) (n : ℕ)

/-- The ordinary double cylinder before collapsing the original base interval. -/
abbrev UnreducedSpace := TopCat.DoubleCylinder.Cylinder (TopCat.ofHom (f.map n))
  (TopCat.ofHom (g.map n))

/-- The full cylinder in the ordinary double mapping cylinder. -/
abbrev unreducedCylinder : A.space n ⊗ TopCat.I ⟶ UnreducedSpace f g n :=
  TopCat.DoubleCylinder.cylinderLine (TopCat.ofHom (f.map n)) (TopCat.ofHom (g.map n))

/-- Both unchanged endpoints in the ordinary double mapping cylinder. -/
abbrev unreducedEnd : TopCat.of (B.space n ⊕ C.space n) ⟶ UnreducedSpace f g n :=
  TopCat.DoubleCylinder.cylinderEnd (TopCat.ofHom (f.map n)) (TopCat.ofHom (g.map n))

/-- The actual ordinary double-cylinder attachment square. -/
theorem unreducedSquare : IsPushout (TopCat.intervalEndpoints (A.space n))
    (DoubleCylinder.endMap (TopCat.ofHom (f.map n)) (TopCat.ofHom (g.map n)))
    (unreducedCylinder f g n) (unreducedEnd f g n) := TopCat.DoubleCylinder.cylinderSquare _ _

/-- Collapse the chosen-point interval to the unchanged reduced homotopy-pushout point. -/
def reduction : UnreducedSpace f g n ⟶ TopCat.of (Space f g n) :=
  (unreducedSquare f g n).desc
    (TopCat.ofHom ⟨fun z : A.space n × TopCat.I ↦ cylinder f g n (z.2.down, z.1), by fun_prop⟩)
    (TopCat.ofHom ⟨Sum.elim (left f g n) (right f g n),
      (left f g n).continuous.sumElim (right f g n).continuous⟩)
    (by
      ext x : 1
      cases x with
      | inl x => exact cylinder_zero f g n x
      | inr x => exact cylinder_one f g n x)

@[simp] theorem reduction_cylinder (x : A.space n) (t : TopCat.I) :
    reduction f g n (unreducedCylinder f g n (x, t)) = cylinder f g n (t.down, x) :=
  ConcreteCategory.congr_hom ((unreducedSquare f g n).inl_desc _ _ _) (x, t)

@[simp] theorem reduction_end (z : B.space n ⊕ C.space n) :
    reduction f g n (unreducedEnd f g n z) = Sum.elim (left f g n) (right f g n) z :=
  ConcreteCategory.congr_hom ((unreducedSquare f g n).inr_desc _ _ _) z

/-- The literal interval collapse used in the reduction square. -/
abbrev intervalToPoint : TopCat.I ⟶ TopCat.of PUnit.{u + 1} :=
  TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

/-- The unchanged chosen-point inclusion of the original reduced quotient. -/
abbrev reducedPoint : TopCat.of PUnit.{u + 1} ⟶ TopCat.of (Space f g n) :=
  TopCat.ofHom (ContinuousMap.const _ (point f g n))

/-- Every point of the original base interval is collapsed. -/
theorem reduction_square :
    DoubleCylinder.baseLine (l := unreducedCylinder f g n) (A.point n) ≫ reduction f g n =
      intervalToPoint ≫ reducedPoint f g n := by
  ext t
  exact (reduction_cylinder f g n (A.point n) t).trans (cylinder_point f g n t.down)

/-- The original quotient is exactly the pushout collapsing its literal base interval. -/
theorem reduction_isPushout :
    IsPushout (DoubleCylinder.baseLine (l := unreducedCylinder f g n) (A.point n))
      intervalToPoint (reduction f g n) (reducedPoint f g n) := by
  have hl (x : A.space n) : unreducedCylinder f g n (x, (0 : TopCat.I)) =
      unreducedEnd f g n (Sum.inl (f.map n x)) :=
    ConcreteCategory.congr_hom (unreducedSquare f g n).w (Sum.inl x)
  have hr (x : A.space n) : unreducedCylinder f g n (x, (1 : TopCat.I)) =
      unreducedEnd f g n (Sum.inr (g.map n x)) :=
    ConcreteCategory.congr_hom (unreducedSquare f g n).w (Sum.inr x)
  let coc := PushoutCocone.mk _ _ (reduction_square f g n)
  apply IsPushout.of_isColimit (c := coc)
  let lift (s : PushoutCocone
      (DoubleCylinder.baseLine (l := unreducedCylinder f g n) (A.point n)) intervalToPoint) :
      TopCat.of (Space f g n) ⟶ s.pt := by
    have hb (t : TopCat.I) : s.inl (unreducedCylinder f g n (A.point n, t)) = s.inr PUnit.unit :=
      ConcreteCategory.congr_hom s.condition t
    have hb₀ : s.inl (unreducedEnd f g n (Sum.inl (B.point n))) = s.inr PUnit.unit := by
      rw [← f.map_point n, ← hl]
      exact hb 0
    exact TopCat.ofHom {
      toFun := Quot.lift (Sum.elim
        (Sum.elim (fun y ↦ s.inl (unreducedEnd f g n (Sum.inl y)))
          (fun z ↦ s.inl (unreducedEnd f g n (Sum.inr z))))
        (fun z ↦ s.inl (unreducedCylinder f g n (z.2, ULift.up z.1)))) (by
          intro a b h
          cases h with
          | left x => exact congrArg s.inl (hl x)
          | right x => exact congrArg s.inl (hr x)
          | base t => exact (hb (ULift.up t)).trans hb₀.symm)
      continuous_toFun := continuous_quot_lift _
        (((show Continuous (fun y ↦ s.inl (unreducedEnd f g n (Sum.inl y))) from
          by fun_prop).sumElim
          (show Continuous (fun z ↦ s.inl (unreducedEnd f g n (Sum.inr z))) from
            by fun_prop)).sumElim (by fun_prop)) }
  have hleft (s) : reduction f g n ≫ lift s = s.inl := by
    apply (unreducedSquare f g n).hom_ext
    · ext ⟨x, t⟩
      change lift s (reduction f g n (unreducedCylinder f g n (x, t))) = _
      rw [reduction_cylinder]
      rfl
    · ext z
      change lift s (reduction f g n (unreducedEnd f g n z)) = _
      rw [reduction_end]
      cases z <;> rfl
  have hright (s) : reducedPoint f g n ≫ lift s = s.inr := by
    ext z
    change s.inl (unreducedEnd f g n (Sum.inl (B.point n))) = s.inr z
    rw [← f.map_point n, ← hl]
    exact ConcreteCategory.congr_hom s.condition (0 : TopCat.I)
  refine PushoutCocone.IsColimit.mk _ lift hleft hright ?_
  intro s m hm _
  ext q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl z =>
      have he := ConcreteCategory.congr_hom hm (unreducedEnd f g n z)
      change m (reduction f g n (unreducedEnd f g n z)) = _ at he
      rw [reduction_end] at he
      cases z <;> exact he
    | inr z =>
      have he := ConcreteCategory.congr_hom hm (unreducedCylinder f g n (z.2, ULift.up z.1))
      change m (reduction f g n (unreducedCylinder f g n (z.2, ULift.up z.1))) = _ at he
      rw [reduction_cylinder] at he
      exact he

/-- Genuine HEP of all three chosen points makes the original reduction a homotopy equivalence. -/
def reductionHomotopyEquiv
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point n))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point n))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point n)))) :
    ContinuousMap.HomotopyEquiv (UnreducedSpace f g n) (Space f g n) := by
  let e : ContinuousMap.HomotopyEquiv TopCat.I PUnit.{u + 1} := {
    toFun := ContinuousMap.const _ PUnit.unit
    invFun := ContinuousMap.const _ 0
    left_inv := ⟨{
      toFun := fun z ↦ ULift.up (z.1 * z.2.down)
      continuous_toFun := by fun_prop
      map_zero_left := fun t ↦ by
        change ULift.up ((0 : unitInterval) * t.down) = (0 : TopCat.I)
        simp only [zero_mul]
        rfl
      map_one_left := fun t ↦ by
        change ULift.up ((1 : unitInterval) * t.down) = t
        simp only [one_mul]
        rfl }⟩
    right_inv := by
      have he : (ContinuousMap.const TopCat.I (PUnit.unit : PUnit.{u + 1})).comp
          (ContinuousMap.const PUnit.{u + 1} (0 : TopCat.I)) = ContinuousMap.id _ := by ext x
      rw [he] }
  exact Pushout.pushoutHomotopyEquivAlongCofibration (reduction_isPushout f g n)
    (DoubleCylinder.homotopyExtensionProperty_baseLine
      (TopCat.ofHom (f.map n)) (TopCat.ofHom (g.map n)) (unreducedSquare f g n)
      (A.point n) (B.point n) (C.point n) (f.map_point n) (g.map_point n) hA hB hC)
    e (by ext t)

@[simp] theorem reductionHomotopyEquiv_toFun
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point n))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point n))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point n)))) :
    (reductionHomotopyEquiv f g n hA hB hC).toFun = (reduction f g n).hom := rfl

/-- The actual reduced homotopy-pushout point inherits genuine HEP from the three original
points. -/
theorem point_homotopyExtensionProperty
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point n))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point n))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point n)))) :
    TopCat.HomotopyExtensionProperty (reducedPoint f g n) :=
  TopCat.homotopyExtensionProperty_pushout (reduction_isPushout f g n)
    (DoubleCylinder.homotopyExtensionProperty_baseLine
      (TopCat.ofHom (f.map n)) (TopCat.ofHom (g.map n)) (unreducedSquare f g n)
      (A.point n) (B.point n) (C.point n) (f.map_point n) (g.map_point n) hA hB hC)

end Topology.LoopPrespectrum.HomotopyPushout

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:32"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.UnreducedSpace

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:36"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.unreducedCylinder

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:40"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.unreducedEnd

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:44"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.unreducedSquare

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:49"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.reduction

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:60"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.reduction_cylinder

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:64"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.reduction_end

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:69"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.intervalToPoint

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:73"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.reducedPoint

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:77"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.reduction_square

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:84"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.reduction_isPushout

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:150"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.reductionHomotopyEquiv

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:182"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.reductionHomotopyEquiv_toFun

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutReduction.lean:193"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.point_homotopyExtensionProperty
