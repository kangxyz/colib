/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalCoefficientTensor
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalRelativeFlatness
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalTensorTerms
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsShortExact
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.StalkRingComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Stalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback

/-! # Tensor exactness for the relative projective-line diagonal

An arbitrary coefficient module pulled back from the second factor preserves
the diagonal ideal sequence. This is a relative flatness statement: on stalks,
the extended coefficient module can be tensored over the stalk on the second
factor, where the diagonal quotient is flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open RingedSpaceModuleAdjunction
open Stacks.PullbackTensorIso (stalkRingEquiv stalkRingEquiv_germ)
open Stacks.SheafOfModules.KFlatStalkCriterion
open Stacks.SheafOfModules.TensorStalkRingedSpace (O ringStalk grpStalk)
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

universe u

private abbrev stalkTensorRing (Z : RingedSpace.{u, u}) (z : Z.carrier) : RingCat.{u} :=
  TopCat.Presheaf.stalk (C := RingCat.{u}) (O Z) z

section Stalks

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

local notation "fᵣ" => f.toLRSHom.toShHom
local notation "Yᵣ" => Y.toRingedSpace
local notation "Xᵣ" => X.toRingedSpace
private abbrev stalkRingHom := (Stacks.RingedSpace.stalkRingMap fᵣ x).hom
local notation "β" => stalkRingHom f x

/-- The two structure sheaf stalk comparisons commute with the stalk maps. -/
private theorem stalkRingEquiv_stalkMap (r : ringStalk Yᵣ (f x)) :
    β (stalkRingEquiv Yᵣ (f x) r) = stalkRingEquiv Xᵣ x (f.stalkMap x r) := by
  obtain ⟨V, hV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := CommRingCat.{u})
    Y.presheaf r
  calc
    _ = β (TopCat.Presheaf.germ (O Yᵣ) V (f x) hV a) :=
      congrArg β (stalkRingEquiv_germ Yᵣ (f x) V hV a)
    _ = TopCat.Presheaf.germ (O Xᵣ) (f ⁻¹ᵁ V) x hV (f.app V a) :=
      Stacks.RingedSpace.stalkRingMap_germ fᵣ x V hV a
    _ = _ := ((congrArg (stalkRingEquiv Xᵣ x) (f.germ_stalkMap_apply V x hV a)).trans
      (stalkRingEquiv_germ Xᵣ x (f ⁻¹ᵁ V) hV (f.app V a))).symm

set_option backward.isDefEq.respectTransparency false in
private theorem stalkFlat_of_isFlatOverAt (F : X.Modules)
    (hf : IsFlatOverAt fᵣ F x) :
    letI := Stacks.RingedSpace.structureStalkCommRing Yᵣ (f x)
    letI := Stacks.RingedSpace.structureStalkCommRing Xᵣ x
    Module.Flat (stalkTensorRing Yᵣ (f x))
      ((ModuleCat.restrictScalars β).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj F)) := by
  let := Stacks.RingedSpace.structureStalkCommRing Yᵣ (f x)
  let := Stacks.RingedSpace.structureStalkCommRing Xᵣ x
  let R := ringStalk Yᵣ (f x)
  let M := grpStalk Xᵣ F.val x
  let : Module R M := Module.compHom _ (f.stalkMap x).hom
  change Module.Flat R M at hf
  let e := stalkRingEquiv Yᵣ (f x)
  let : Algebra (stalkTensorRing Yᵣ (f x)) R := e.symm.toRingHom.toAlgebra
  let : Module (stalkTensorRing Yᵣ (f x)) M :=
    Module.compHom _ β
  change Module.Flat (stalkTensorRing Yᵣ (f x)) M
  have : Module.Flat (stalkTensorRing Yᵣ (f x)) R :=
    RingHom.Flat.of_bijective e.symm.bijective
  have : IsScalarTower (stalkTensorRing Yᵣ (f x)) R M := by
    refine IsScalarTower.of_algebraMap_smul fun r m => ?_
    change (f.stalkMap x).hom (e.symm r) • m = β r • m
    have hβ : β r = stalkRingEquiv Xᵣ x ((f.stalkMap x).hom (e.symm r)) :=
      (congrArg β (e.apply_symm_apply r).symm).trans
        (stalkRingEquiv_stalkMap f x (e.symm r))
    rw [hβ]
    exact (Stacks.PullbackTensorIso.smul_stalkRingEquiv (Z := Xᵣ) (z := x) F _ m).symm
  exact Module.Flat.trans (stalkTensorRing Yᵣ (f x)) R M

end Stalks

section RingedStalk

variable {U V : RingedSpace.{u, u}} (f : U ⟶ V) (x : U.carrier)

local notation "R" => stalkTensorRing V (f.hom.base x)
local notation "A" => stalkTensorRing U x
private abbrev stalkFunctorAt (W : RingedSpace.{u, u}) (w : W.carrier) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor.{u} (structureSheafRing W) w

local notation "F" => stalkFunctorAt U x
local notation "G" => stalkFunctorAt V (f.hom.base x)

private theorem stalkFunctor_zero' :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor.{u}
      (structureSheafRing U) x).PreservesZeroMorphisms := by
  let : (AlgebraicGeometry.SheafOfModules.stalkFunctor.{u}
      (structureSheafRing U) x).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive (structureSheafRing U) x
  exact Functor.preservesZeroMorphisms_of_additive _

private theorem stalkTensorRight_zero' (E : _root_.SheafOfModules.{u} (structureSheafRing U)) :
    Functor.PreservesZeroMorphisms
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).flip.obj E) :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorFlipObj U.sheaf E

set_option backward.isDefEq.respectTransparency false in
private theorem stalkShortExact_tensorPullback
    (S : ShortComplex (_root_.SheafOfModules.{u} (structureSheafRing U)))
    (hS : (@ShortComplex.map _ _ _ _ _ _ S F (stalkFunctor_zero' (U := U) x)).ShortExact)
    (E : _root_.SheafOfModules.{u} (structureSheafRing V)) :
    letI : (F).PreservesZeroMorphisms := stalkFunctor_zero' (U := U) x
    letI : CommRing (ToType R) := Stacks.RingedSpace.structureStalkCommRing V (f.hom.base x)
    letI : CommRing (ToType A) := Stacks.RingedSpace.structureStalkCommRing U x
    Module.Flat (ToType R)
      ((ModuleCat.restrictScalars (Stacks.RingedSpace.stalkRingMap f x).hom).obj
        ((F).obj S.X₃)) →
      ((S.map F).map (tensorRight ((F).obj ((modulePullback f).obj E)))).ShortExact := by
  let : CommRing (ToType R) := Stacks.RingedSpace.structureStalkCommRing V (f.hom.base x)
  let : CommRing (ToType A) := Stacks.RingedSpace.structureStalkCommRing U x
  let : (F).PreservesZeroMorphisms := stalkFunctor_zero' (U := U) x
  intro hflat
  let β : ToType R →+* ToType A := (Stacks.RingedSpace.stalkRingMap f x).hom
  let N : ModuleCat (ToType R) := (G).obj E
  let N' : ModuleCat (ToType A) := (ModuleCat.extendScalars β).obj N
  have e : (F).obj ((modulePullback f).obj E) ≅ N' :=
    (Stacks.RingedSpace.stalkModulePullbackFunctorIso f x).app E
  apply ShortComplex.shortExact_of_iso
    (((S.map F).mapNatIso ((MonoidalCategory.curriedTensor _).flip.mapIso e)).symm)
  exact shortExact_tensorRight_extendScalars β (S.map F) hS N hflat

set_option backward.isDefEq.respectTransparency false in
private theorem stalkShortExact_tensorRight
    (S : ShortComplex (_root_.SheafOfModules.{u} (structureSheafRing U)))
    (E : _root_.SheafOfModules.{u} (structureSheafRing U)) :
    letI : (F).PreservesZeroMorphisms := stalkFunctor_zero' (U := U) x
    let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).flip.obj E
    letI : T.PreservesZeroMorphisms := stalkTensorRight_zero' (U := U) E
    letI : CommRing (ToType (stalkTensorRing U x)) :=
      Stacks.RingedSpace.structureStalkCommRing U x
    (S.map (F ⋙ tensorRight ((F).obj E))).ShortExact →
      (S.map (T ⋙ F)).ShortExact := by
  let : (F).PreservesZeroMorphisms := stalkFunctor_zero' (U := U) x
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).flip.obj E
  let : T.PreservesZeroMorphisms := stalkTensorRight_zero' (U := U) E
  let : CommRing (ToType (stalkTensorRing U x)) :=
    Stacks.RingedSpace.structureStalkCommRing U x
  change (S.map (F ⋙ tensorRight ((F).obj E))).ShortExact →
    (S.map (T ⋙ F)).ShortExact
  intro h
  have e : T ⋙ F ≅ F ⋙ tensorRight ((F).obj E) :=
    NatIso.ofComponents (fun M => stalkTensorIso U x M E) fun g =>
      stalkTensorIso_naturality_left U x g E
  exact ShortComplex.shortExact_of_iso (S.mapNatIso e).symm h

end RingedStalk

section Tensor

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => pullback π π
local notation "p₂" => pullback.snd π π
local notation "S" => projectiveLineDiagonalSequence X

instance projectiveLineDiagonalCoefficientFunctor_preservesZeroMorphisms
    (E : (P).Modules) :
    (projectiveLineDiagonalCoefficientFunctor X E).PreservesZeroMorphisms :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorFlipObj (Q).sheaf
    ((Modules.pullback p₂).obj E)

set_option backward.isDefEq.respectTransparency false in
/-- The relative diagonal sequence remains short exact after tensoring with the pullback of
an arbitrary coefficient module from the second factor. -/
theorem projectiveLineDiagonalSequence_tensor_shortExact (E : (P).Modules) :
    (@ShortComplex.map _ _ _ _ _ _ (S) (projectiveLineDiagonalCoefficientFunctor X E)
      (projectiveLineDiagonalCoefficientFunctor_preservesZeroMorphisms X E)).ShortExact := by
  apply (Stacks.SheafOfModules.shortExact_iff_forall_stalkAb _).2
  intro y
  let f := (p₂).toLRSHom.toShHom
  let Qᵣ := (Q).toRingedSpace
  let Pᵣ := (P).toRingedSpace
  let := Stacks.RingedSpace.structureStalkCommRing Qᵣ y
  let := Stacks.RingedSpace.structureStalkCommRing Pᵣ (p₂ y)
  let U := AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Qᵣ) y
  let E' := (Modules.pullback p₂).obj E
  have : U.Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive (structureSheafRing Qᵣ) y
  have : PreservesFiniteLimits U :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits (structureSheafRing Qᵣ) y
  have : PreservesColimits U :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits (structureSheafRing Qᵣ) y
  have hU := (projectiveLineDiagonalSequence_shortExact X).map_of_exact U
  have hflat :=
    stalkFlat_of_isFlatOverAt p₂ y (S).X₃ (projectiveLineDiagonalQuotient_isFlatOver X y)
  have hstalk := stalkShortExact_tensorPullback (U := Qᵣ) (V := Pᵣ) f y (S) hU E hflat
  change (((S).map U).map (tensorRight (U.obj E'))).ShortExact at hstalk
  have h1 : ((S).map (U ⋙ tensorRight (U.obj E'))).ShortExact := hstalk
  let T := projectiveLineDiagonalCoefficientFunctor X E
  let : T.PreservesZeroMorphisms :=
    projectiveLineDiagonalCoefficientFunctor_preservesZeroMorphisms X E
  let : (T ⋙ U).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp T U
  have h2 : ((S).map (T ⋙ U)).ShortExact := by
    exact stalkShortExact_tensorRight (U := Qᵣ) y (S) E' h1
  let A := forget₂ (ModuleCat (stalkTensorRing Qᵣ y)) AddCommGrpCat
  let e : U ⋙ A ≅ Stacks.SheafOfModules.stalkAbFunctor Q y := eqToIso (by
    change AlgebraicGeometry.SheafOfModules.stalkFunctor (Q).ringCatSheaf y ⋙ A =
      Stacks.SheafOfModules.stalkAbFunctor Q y
    rw [Stacks.SheafOfModules.stalkAbFunctor_eq]
    exact AlgebraicGeometry.SheafOfModules.stalkFunctor_comp_forget₂ (Q).ringCatSheaf y)
  apply ShortComplex.shortExact_of_iso (((S).map T).mapNatIso e)
  exact h2.map_of_exact A

end Tensor

end AlgebraicGeometry.Scheme
