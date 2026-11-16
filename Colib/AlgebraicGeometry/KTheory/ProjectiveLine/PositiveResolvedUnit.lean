/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PositiveUnit
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.PositiveDerivedUnit
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricCoefficientFunctors
public import Colib.KTheory.Waldhausen.Functoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise

/-! # The resolved positive unit is a quasi-isomorphism

The actual chain map from the positive coefficient construction is identified with the
native derived adjunction unit via the flat pullback comparison and the flasque direct
image comparison. The two maps agree by the derived-unit factorization and naturality.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [Flat f] [IsProper f] [LocallyOfFinitePresentation f]

local notation "c" => ComplexShape.up ℤ

/-- The actual resolved chain unit is weak when the corresponding derived unit is invertible. -/
theorem resolvedPullbackUnitChain_quasiIso_of_isIso (K : BoundedBelowPerfect.Obj Y)
    (hη : IsIso ((derivedAdjunction f.toLRSHom.toShHom).unit.app (DerivedCategory.Q.obj K.obj))) :
    QuasiIso (resolvedPullbackUnitChain f K) := by
  let φ := f.toLRSHom.toShHom
  let η := (derivedAdjunction φ).unit
  let R := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward φ
  let A := (pullback f).mapHomologicalComplex c
  let B := (pushforward f).mapHomologicalComplex c
  let qY := HomotopyCategory.quotient Y.Modules c
  let qX := HomotopyCategory.quotient X.Modules c
  let K₀ := (BoundedBelowPerfect.flatPullback f).obj K
  let J := (total X).obj K₀
  let s : A.obj K.obj ⟶ J.obj := ((BoundedBelowPerfect.godementUnit X).app K₀).hom
  let t := ((pullbackPushforwardAdjunction f).mapHomologicalComplexAdjunction c).unit.app K.obj
  let α := (derivedPullbackComparison φ).app (qY.obj K.obj)
  let β := derivedPushforwardModulesUnit f
  have hη' : IsIso (η.app (DerivedCategory.Qh.obj (qY.obj K.obj))) := by
    let e := (DerivedCategory.quotientCompQhIso Y.Modules).hom.app K.obj
    have h : e ≫ η.app (DerivedCategory.Q.obj K.obj) =
        η.app (DerivedCategory.Qh.obj (qY.obj K.obj)) ≫ (derivedPullback φ ⋙ R).map e :=
      η.naturality e
    let : IsIso (η.app (DerivedCategory.Qh.obj (qY.obj K.obj)) ≫
        (derivedPullback φ ⋙ R).map
          ((DerivedCategory.quotientCompQhIso Y.Modules).hom.app K.obj)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right (η.app (DerivedCategory.Qh.obj (qY.obj K.obj)))
      ((derivedPullback φ ⋙ R).map ((DerivedCategory.quotientCompQhIso Y.Modules).hom.app K.obj))
  have hα : IsIso α :=
    Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackComparison_app_of_isFlat φ
      (fun x => Flat.stalkMap f x) _
  have hs : IsIso (DerivedCategory.Qh.map (qX.map s)) := by
    have h := BoundedBelowPerfect.godementUnit_quasiIso K₀
    have h' : IsIso (DerivedCategory.Q.map s) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules s).2 h
    have hn := DerivedCategory.quotientCompQhIso_hom_naturality s
    let : IsIso (DerivedCategory.Qh.map (qX.map s) ≫
        (DerivedCategory.quotientCompQhIso X.Modules).hom.app J.obj) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right (DerivedCategory.Qh.map (qX.map s))
      ((DerivedCategory.quotientCompQhIso X.Modules).hom.app J.obj)
  have hβ : IsIso (β.app (qX.obj J.obj)) :=
    isIso_flasquePushforwardUnit_app f J.obj J.property.1.2 J.property.2
  have hfac : η.app (DerivedCategory.Qh.obj (qY.obj K.obj)) ≫ R.map α =
      DerivedCategory.Qh.map (qY.map t) ≫ β.app (qX.obj (A.obj K.obj)) := by
    exact derivedAdjunction_unit_fac φ (qY.obj K.obj)
  have hnat : DerivedCategory.Qh.map (qY.map (B.map s)) ≫ β.app (qX.obj J.obj) =
      β.app (qX.obj (A.obj K.obj)) ≫ R.map (DerivedCategory.Qh.map (qX.map s)) := by
    have h := β.naturality (qX.map s)
    have hm : ((pushforward f).mapHomotopyCategory c).map (qX.map s) =
        qY.map (B.map s) := Functor.mapHomotopyCategory_map (pushforward f) s
    change DerivedCategory.Qh.map (((pushforward f).mapHomotopyCategory c).map (qX.map s)) ≫
        β.app (qX.obj J.obj) =
      β.app (qX.obj (A.obj K.obj)) ≫ R.map (DerivedCategory.Qh.map (qX.map s)) at h
    rw [hm] at h
    exact h
  have hcmp : DerivedCategory.Qh.map (qY.map (t ≫ B.map s)) ≫ β.app (qX.obj J.obj) =
      (η.app (DerivedCategory.Qh.obj (qY.obj K.obj)) ≫ R.map α) ≫
        R.map (DerivedCategory.Qh.map (qX.map s)) := by
    rw [qY.map_comp, DerivedCategory.Qh.map_comp, Category.assoc, hnat,
      ← Category.assoc, ← hfac]
  have hq : IsIso (DerivedCategory.Qh.map (qY.map (t ≫ B.map s))) := by
    let : IsIso (DerivedCategory.Qh.map (qY.map (t ≫ B.map s)) ≫ β.app (qX.obj J.obj)) := by
      rw [hcmp]
      infer_instance
    exact IsIso.of_isIso_comp_right (DerivedCategory.Qh.map (qY.map (t ≫ B.map s)))
      (β.app (qX.obj J.obj))
  have hQ : IsIso (DerivedCategory.Q.map (t ≫ B.map s)) := by
    have hn : DerivedCategory.Qh.map (qY.map (t ≫ B.map s)) ≫
        (DerivedCategory.quotientCompQhIso Y.Modules).hom.app (B.obj J.obj) =
        (DerivedCategory.quotientCompQhIso Y.Modules).hom.app K.obj ≫
          DerivedCategory.Q.map (t ≫ B.map s) :=
      DerivedCategory.quotientCompQhIso_hom_naturality (t ≫ B.map s)
    let : IsIso ((DerivedCategory.quotientCompQhIso Y.Modules).hom.app K.obj ≫
        DerivedCategory.Q.map (t ≫ B.map s)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_left ((DerivedCategory.quotientCompQhIso Y.Modules).hom.app K.obj)
      (DerivedCategory.Q.map (t ≫ B.map s))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso Y.Modules _).1 hQ

section ProjectiveLine

variable (S : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 S
local notation "π" => (P ↘ S)

local instance : IsProper π := isProper_projectiveSpaceOver 1 S

/-- The positive coefficient unit is weak on each bounded below perfect complex. -/
theorem projectiveLineResolvedPullbackUnit_quasiIso (K : BoundedBelowPerfect.Obj S) :
    QuasiIso (resolvedPullbackUnitChain π K) :=
  resolvedPullbackUnitChain_quasiIso_of_isIso π K
    (projectiveLineDerivedUnit_isIso S _ K.property.1.isPerfect)

/-- The positive diagonal coefficient equals the actual bounded-below inclusion on K-groups. -/
theorem projectiveLineG₀_untwisted_KMap (n : ℕ) :
    KMap (((BoundedBelowPerfect.flatPullback_exact π).comp (total_exact P)).comp
      (projectiveLineG₀_exact S)) n = KMap (BoundedBelowPerfect.inclusion_exact S) n :=
  (KMap_eq_of_weakNatTrans (BoundedBelowPerfect.inclusion_exact S) _
    (resolvedPullbackUnit π)
    (fun K => projectiveLineResolvedPullbackUnit_quasiIso S K) n).symm

end ProjectiveLine

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
