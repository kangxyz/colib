/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.FiniteIsomorphisms
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.PullbackComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic

/-!
# Descent of tensor-power equations for specified isomorphisms

The transfer below retains the native tensor-power and pullback comparisons. Its composition
law is the two-module version of the native tensor-power transfer law. It permits reflection of
power equations after descending an actual isomorphism, rather than assuming a stage frame.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u v w w'

namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance (X : Scheme.{u}) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- Transfer an isomorphism between two pulled-back invertible modules to their powers. -/
def pullbackPowerIso {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property A]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property B]
    (e : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) (n : ℕ) :
    (Scheme.Modules.pullback f).obj
        (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
          A (n : ℤ)) ≅
      (Scheme.Modules.pullback f).obj
        (tensorPower Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
          B (n : ℤ)) :=
  Scheme.Modules.pullbackTensorPowerIso f A n ≪≫
    tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
      _ _ e n ≪≫ (Scheme.Modules.pullbackTensorPowerIso f B n).symm

/-- The transfer of powers commutes with a further pullback and the original canonical
comparison. This is the native transfer calculation with two possibly different modules. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/AmpleTransport/PullbackComp.lean:391-437" "adaptation"
  "Tensor-power transfer under a further pullback for two different invertible modules"]
theorem pullbackPowerIso_canStep {X Y Z : Scheme.{u}} (q : X ⟶ Y) (f : Y ⟶ Z)
    (p : X ⟶ Z) (hp : q ≫ f = p) (A B : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property A]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property B]
    (e : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) (n : ℕ) :
    (canIso q f p hp
      (tensorPower Z.toRingedSpace.presheaf (structureSheafRing Z.toRingedSpace).property
        A (n : ℤ))).inv ≫
      (Scheme.Modules.pullback q).map (pullbackPowerIso f A B e n).hom ≫
      (canIso q f p hp
        (tensorPower Z.toRingedSpace.presheaf (structureSheafRing Z.toRingedSpace).property
          B (n : ℤ))).hom =
    (pullbackPowerIso p A B ((canIso q f p hp A).symm ≪≫
      (Scheme.Modules.pullback q).mapIso e ≪≫ canIso q f p hp B) n).hom := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback q).obj A) :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback f).obj A)))
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback q).obj B) :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback f).obj B)))
  subst p
  have hcan (L : Z.Modules) : canIso q f (q ≫ f) rfl L =
      (Scheme.Modules.pullbackComp q f).app L := Iso.ext (canHom_rfl q f L)
  simp only [hcan]
  exact Scheme.Modules.tensorPowerTransfer_pullback_aux (Scheme.Modules.pullback q)
    ((Scheme.Modules.pullbackComp q f).app _).symm
    ((Scheme.Modules.pullbackComp q f).app _).symm
    _ _ _ _ _ _ _ _ _ _ _
    (Scheme.Modules.pullbackTensorPowerIso_comp q f A n)
    (Scheme.Modules.pullbackTensorPowerIso_comp q f B n)
    (Scheme.Modules.pullbackTensorPowerIso_naturality q e n)
    ((tensorPowerCongr_trans X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullbackComp q f).app A).symm
      ((Scheme.Modules.pullback q).mapIso e ≪≫ (Scheme.Modules.pullbackComp q f).app B) n).trans
      (congrArg₂ (· ≪≫ ·)
        (tensorPowerCongr_symm X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          ((Scheme.Modules.pullbackComp q f).app A) n)
        (tensorPowerCongr_trans X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          ((Scheme.Modules.pullback q).mapIso e) ((Scheme.Modules.pullbackComp q f).app B) n)))

private theorem iso_eq_of_square {C : Type*} [Category C] {A B A' B' : C}
    (a : A ≅ A') (b : B ≅ B') (m : A ≅ B) (N : A' ≅ B')
    (h : m.hom ≫ b.hom = a.hom ≫ N.hom) : a.symm ≪≫ m ≪≫ b = N := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [h, Iso.inv_hom_id_assoc]

private theorem conjugate_eq_of_square {C : Type*} [Category C] {A B A' B' : C}
    (a : A ≅ A') (b : B ≅ B') (m : A ⟶ B) (N : A' ⟶ B')
    (h : m ≫ b.hom = a.hom ≫ N) : a.inv ≫ m ≫ b.hom = N := by
  rw [h, Iso.inv_hom_id_assoc]

private theorem eq_of_conjugates {C : Type*} [Category C] {A B A' B' : C}
    (a : A ≅ A') (b : B ≅ B') (m m' : A ⟶ B)
    (h : a.inv ≫ m ≫ b.hom = a.inv ≫ m' ≫ b.hom) : m = m' := by
  simpa only [cancel_epi, cancel_mono] using h

set_option maxHeartbeats 600000 in
-- The final comparison elaborates three nested scheme-module pullbacks and their tensor powers.
/-- An actual limit isomorphism descends with a finite family of prescribed power equations.
The same original power morphisms occur in the conclusion, and all equations hold at one
transition. In particular the target can be a structure sheaf, so the isomorphism is a frame
under the native unit-pullback comparison. -/
@[colib_tag "COL-1101"]
theorem exists_iso_pullback_power_comp_eq_of_isLimit_finite
    {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I) (A B : (D.obj i).Modules)
    [hA : AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj i).toRingedSpace.presheaf
      (structureSheafRing (D.obj i).toRingedSpace).property A]
    [hB : AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj i).toRingedSpace.presheaf
      (structureSheafRing (D.obj i).toRingedSpace).property B]
    (N : (Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B)
    {κ : Type w} [Finite κ] (n : κ → ℕ)
    (α : ∀ x, tensorPower (D.obj i).toRingedSpace.presheaf
        (structureSheafRing (D.obj i).toRingedSpace).property A (n x : ℤ) ⟶
      tensorPower (D.obj i).toRingedSpace.presheaf
        (structureSheafRing (D.obj i).toRingedSpace).property B (n x : ℤ))
    (hα : ∀ x, (pullbackPowerIso (c.π.app i) A B N (n x)).hom =
      (Scheme.Modules.pullback (c.π.app i)).map (α x))
    {η : Type w'} [Finite η] (P : η → (D.obj i).Modules)
    [∀ x, (P x).IsFinitePresentation] (s : ∀ x, P x ⟶ A) (t : ∀ x, P x ⟶ B)
    (hst : ∀ x, (Scheme.Modules.pullback (c.π.app i)).map (s x) ≫ N.hom =
      (Scheme.Modules.pullback (c.π.app i)).map (t x)) :
    ∃ (j : I) (f : j ⟶ i)
      (m : (Scheme.Modules.pullback (D.map f)).obj A ≅
        (Scheme.Modules.pullback (D.map f)).obj B),
      ((Scheme.Modules.pullback (c.π.app j)).map m.hom ≫
          canHom (c.π.app j) (D.map f) (c.π.app i) (c.w f) B =
        canHom (c.π.app j) (D.map f) (c.π.app i) (c.w f) A ≫ N.hom) ∧
      (∀ x, (pullbackPowerIso (D.map f) A B m (n x)).hom =
        (Scheme.Modules.pullback (D.map f)).map (α x)) ∧
      ∀ x, (Scheme.Modules.pullback (D.map f)).map (s x) ≫ m.hom =
        (Scheme.Modules.pullback (D.map f)).map (t x) := by
  have : A.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible _ A hA
  have : B.IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible _ B hB
  obtain ⟨j, f, m, hm, hmt⟩ :=
    exists_iso_pullback_canonical_comp_eq_of_isLimit_finite D c hc i A B N P s t hst
  let PA (x : κ) : (D.obj i).Modules := tensorPower (D.obj i).toRingedSpace.presheaf
    (structureSheafRing (D.obj i).toRingedSpace).property A (n x : ℤ)
  let PB (x : κ) : (D.obj i).Modules := tensorPower (D.obj i).toRingedSpace.presheaf
    (structureSheafRing (D.obj i).toRingedSpace).property B (n x : ℤ)
  have hPA (x : κ) : (PA x).IsFinitePresentation := by
    have h := tensorPower_isInvertible (D.obj i).toRingedSpace.presheaf
      (structureSheafRing (D.obj i).toRingedSpace).property A (n x : ℤ)
    exact @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible _ (PA x)
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ h)
  have hPB (x : κ) : (PB x).IsFinitePresentation := by
    have h := tensorPower_isInvertible (D.obj i).toRingedSpace.presheaf
      (structureSheafRing (D.obj i).toRingedSpace).property B (n x : ℤ)
    exact @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible _ (PB x)
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ h)
  have hN := iso_eq_of_square (canIso (c.π.app j) (D.map f) (c.π.app i) (c.w f) A)
    (canIso (c.π.app j) (D.map f) (c.π.app i) (c.w f) B)
    ((Scheme.Modules.pullback (c.π.app j)).mapIso m) N hm
  have heq (x : κ) : (Scheme.Modules.pullback (c.π.app j)).map
        (pullbackPowerIso (D.map f) A B m (n x)).hom =
      (Scheme.Modules.pullback (c.π.app j)).map
        ((Scheme.Modules.pullback (D.map f)).map (α x)) := by
    apply eq_of_conjugates
      (canIso (c.π.app j) (D.map f) (c.π.app i) (c.w f) (PA x))
      (canIso (c.π.app j) (D.map f) (c.π.app i) (c.w f) (PB x))
    exact (pullbackPowerIso_canStep (c.π.app j) (D.map f) (c.π.app i) (c.w f)
      A B m (n x)).trans
      ((congrArg (fun e => (pullbackPowerIso (c.π.app i) A B e (n x)).hom) hN).trans
        ((hα x).trans (conjugate_eq_of_square
          (canIso (c.π.app j) (D.map f) (c.π.app i) (c.w f) (PA x))
          (canIso (c.π.app j) (D.map f) (c.π.app i) (c.w f) (PB x)) _ _
          (canHom_naturality (c.π.app j) (D.map f) (c.π.app i) (c.w f) (α x))).symm))
  have : ∀ x, ((Scheme.Modules.pullback (D.map f)).obj (PA x)).IsFinitePresentation :=
    fun x => isFinitePresentation_pullback _ (PA x)
  have : ∀ x, ((Scheme.Modules.pullback (D.map f)).obj (PB x)).IsFinitePresentation :=
    fun x => isFinitePresentation_pullback _ (PB x)
  obtain ⟨k, g, hg⟩ := exists_pullback_map_eq_of_isLimit_finite D c hc j
    (fun x => (Scheme.Modules.pullback (D.map f)).obj (PA x))
    (fun x => (Scheme.Modules.pullback (D.map f)).obj (PB x))
    (fun x => (pullbackPowerIso (D.map f) A B m (n x)).hom)
    (fun x => (Scheme.Modules.pullback (D.map f)).map (α x)) heq
  let mf := (canIso (D.map g) (D.map f) (D.map (g ≫ f)) (D.map_comp g f).symm A).symm ≪≫
    (Scheme.Modules.pullback (D.map g)).mapIso m ≪≫
      canIso (D.map g) (D.map f) (D.map (g ≫ f)) (D.map_comp g f).symm B
  refine ⟨k, g ≫ f, mf, ?_, (fun x => ?_), fun x => ?_⟩
  · exact canonical_eq_of_further_step (c.π.app k) (D.map g) (c.π.app j) (c.w g)
      (D.map f) (c.π.app i) (c.w f) (D.map (g ≫ f)) (D.map_comp g f).symm
      (c.w (g ≫ f)) m.hom N.hom hm
  · exact (pullbackPowerIso_canStep (D.map g) (D.map f) (D.map (g ≫ f))
      (D.map_comp g f).symm A B m (n x)).symm.trans
      ((congrArg (fun z =>
        (canIso (D.map g) (D.map f) (D.map (g ≫ f)) (D.map_comp g f).symm (PA x)).inv ≫
          z ≫ (canIso (D.map g) (D.map f) (D.map (g ≫ f))
            (D.map_comp g f).symm (PB x)).hom) (hg x)).trans
        (conjugate_eq_of_square
          (canIso (D.map g) (D.map f) (D.map (g ≫ f)) (D.map_comp g f).symm (PA x))
          (canIso (D.map g) (D.map f) (D.map (g ≫ f)) (D.map_comp g f).symm (PB x)) _ _
          (canHom_naturality (D.map g) (D.map f) (D.map (g ≫ f))
            (D.map_comp g f).symm (α x))))
  · refine (cancel_epi (canHom (D.map g) (D.map f) (D.map (g ≫ f))
      (D.map_comp g f).symm (P x))).mp ?_
    change _ ≫ _ ≫ canStep _ _ _ _ m.hom = _
    rw [← Category.assoc, ← canHom_naturality _ _ _ _ (s x),
      ← canHom_naturality _ _ _ _ (t x), canStep]
    simp only [Category.assoc, ← canIso_hom]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← Functor.map_comp, hmt x,
      canIso_hom]

end Stacks.AlgebraicGeometry.ModuleLimits
