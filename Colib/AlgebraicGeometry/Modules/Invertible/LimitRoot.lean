/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.FiniteIsomorphisms
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic

/-!
# Descent of an actual tensor-power root

An invertible module on a cofiltered qcqs limit is first descended over a specified stage.
Its specified tensor-power isomorphism then descends at a further stage. The conclusion keeps
both transition maps and the canonical equation identifying the descended isomorphism with the
original one. The target is the iterated pullback of the original stage module; `canIso` identifies
it with pullback along the composite transition.

No root or frame at a stage is assumed. This is a root-descent result on a specified compatible
scheme diagram. Descent of a separate boundary embedding, its frame, and the tensor-power equation
on that whole boundary requires the corresponding compatible diagram and is not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

local instance (X : Scheme.{u}) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL

local instance (X : Scheme.{u}) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L := hL

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

private theorem iso_trans_cancel {C : Type*} [Category C] {A B D E F : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : F ≅ E) :
    (a ≪≫ b ≪≫ c ≪≫ d.symm).hom ≫ d.hom = a.hom ≫ b.hom ≫ c.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- An actual invertible root of the pullback of a finitely presented stage module descends.
The root comparison is retained, not merely its Picard class. The displayed equation uses the
original cone legs, original power isomorphism, and native pullback/tensor-power comparisons. -/
@[colib_tag "COL-1087", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/ModuleLimits/InvertibleUnconditional.lean:191-203"
  "ingredient" "Descent of the actual invertible module before descending its power isomorphism"]
theorem exists_tensorPower_root_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I) (L : (D.obj i).Modules)
    [L.IsFinitePresentation] (M : c.pt.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible
      c.pt.sheaf.obj c.pt.ringCatSheaf.property M]
    (n : ℕ)
    (α : tensorPower c.pt.sheaf.obj c.pt.ringCatSheaf.property M (n : ℤ) ≅
      (Scheme.Modules.pullback (c.π.app i)).obj L) :
    ∃ (k : I) (e : k ⟶ i) (Mk : (D.obj k).Modules)
      (hMk : AlgebraicGeometry.SheafOfModules.IsInvertible
        (D.obj k).sheaf.obj (D.obj k).ringCatSheaf.property Mk),
      let _ := hMk
      ∃ (eM : M ≅ (Scheme.Modules.pullback (c.π.app k)).obj Mk) (j : I) (f : j ⟶ k)
        (β : tensorPower (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property
            ((Scheme.Modules.pullback (D.map f)).obj Mk) (n : ℤ) ≅
          (Scheme.Modules.pullback (D.map f)).obj
            ((Scheme.Modules.pullback (D.map e)).obj L)),
        (Scheme.Modules.pullback (c.π.app j)).map
            ((Scheme.Modules.pullbackTensorPowerIso (D.map f) Mk n).hom ≫ β.hom) ≫
          canHom (c.π.app j) (D.map f) (c.π.app k) (c.w f)
            ((Scheme.Modules.pullback (D.map e)).obj L) ≫
          canHom (c.π.app k) (D.map e) (c.π.app i) (c.w e) L =
        canHom (c.π.app j) (D.map f) (c.π.app k) (c.w f)
            (tensorPower (D.obj k).sheaf.obj (D.obj k).ringCatSheaf.property Mk (n : ℤ)) ≫
          (Scheme.Modules.pullbackTensorPowerIso (c.π.app k) Mk n).hom ≫
          (tensorPowerCongr c.pt.sheaf.obj c.pt.ringCatSheaf.property _ _ eM.symm n).hom ≫
          α.hom := by
  have hc' : IsLimit (c.whisker (Over.forget i)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have : ∀ {j k : Over i} (f : j ⟶ k), IsAffineHom ((Over.forget i ⋙ D).map f) :=
    fun f => inferInstanceAs (IsAffineHom (D.map f.left))
  have : ∀ j : Over i, CompactSpace ((Over.forget i ⋙ D).obj j) :=
    fun j => inferInstanceAs (CompactSpace (D.obj j.left))
  have : ∀ j : Over i, QuasiSeparatedSpace ((Over.forget i ⋙ D).obj j) :=
    fun j => inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  obtain ⟨k, Mk, hMk, ⟨eM⟩⟩ := exists_isInvertible_pullback_iso_of_isLimit
    (Over.forget i ⋙ D) (c.whisker (Over.forget i)) hc' M hM
  change AlgebraicGeometry.SheafOfModules.IsInvertible
    (D.obj k.left).sheaf.obj (D.obj k.left).ringCatSheaf.property Mk at hMk
  change M ≅ (Scheme.Modules.pullback (c.π.app k.left)).obj Mk at eM
  let := hMk
  let P : (D.obj k.left).Modules :=
    tensorPower (D.obj k.left).sheaf.obj (D.obj k.left).ringCatSheaf.property Mk (n : ℤ)
  let Q := (Scheme.Modules.pullback (D.map k.hom)).obj L
  have hP : P.IsFinitePresentation := by
    have hPInv := tensorPower_isInvertible (D.obj k.left).sheaf.obj
      (D.obj k.left).ringCatSheaf.property Mk (n : ℤ)
    have : AlgebraicGeometry.SheafOfModules.IsInvertible
        (D.obj k.left).sheaf.obj (D.obj k.left).ringCatSheaf.property P :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hPInv
    exact @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible
      (D.obj k.left) P this
  have hQ : Q.IsFinitePresentation := isFinitePresentation_pullback _ L
  let N : (Scheme.Modules.pullback (c.π.app k.left)).obj P ≅
      (Scheme.Modules.pullback (c.π.app k.left)).obj Q :=
    Scheme.Modules.pullbackTensorPowerIso (c.π.app k.left) Mk n ≪≫
      tensorPowerCongr c.pt.sheaf.obj c.pt.ringCatSheaf.property _ _ eM.symm n ≪≫
      α ≪≫ (canIso (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) L).symm
  obtain ⟨j, f, β, hβ⟩ := @exists_iso_pullback_canonical_of_isLimit
    _ _ _ D _ c _ _ hc k.left P Q hP hQ N
  refine ⟨k.left, k.hom, Mk, hMk, eM, j, f,
    (Scheme.Modules.pullbackTensorPowerIso (D.map f) Mk n).symm ≪≫ β, ?_⟩
  have hcancel : (Scheme.Modules.pullbackTensorPowerIso (D.map f) Mk n).hom ≫
      ((Scheme.Modules.pullbackTensorPowerIso (D.map f) Mk n).symm ≪≫ β).hom = β.hom :=
    Iso.hom_inv_id_assoc _ _
  refine (congrArg (fun z => (Scheme.Modules.pullback (c.π.app j)).map z ≫
    canHom (c.π.app j) (D.map f) (c.π.app k.left) (c.w f) Q ≫
    canHom (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) L) hcancel).trans ?_
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫
      canHom (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) L) hβ).trans ?_)
  exact (Category.assoc _ _ _).trans (congrArg
    (fun z => canHom (c.π.app j) (D.map f) (c.π.app k.left) (c.w f) P ≫ z)
    (iso_trans_cancel (Scheme.Modules.pullbackTensorPowerIso (c.π.app k.left) Mk n)
      (tensorPowerCongr c.pt.sheaf.obj c.pt.ringCatSheaf.property _ _ eM.symm n) α
      (canIso (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) L)))

/-- The descended root, with its target expressed as pullback along a single composite
transition. `exists_tensorPower_root_of_isLimit` additionally retains the original limit equation.
The exponent is allowed to be zero; in particular every specified positive-power root descends. -/
@[colib_tag "COL-1087"]
theorem exists_tensorPower_root_pullback_iso_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I) (L : (D.obj i).Modules)
    [L.IsFinitePresentation] (M : c.pt.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible
      c.pt.sheaf.obj c.pt.ringCatSheaf.property M]
    (n : ℕ)
    (α : tensorPower c.pt.sheaf.obj c.pt.ringCatSheaf.property M (n : ℤ) ≅
      (Scheme.Modules.pullback (c.π.app i)).obj L) :
    ∃ (j : I) (e : j ⟶ i) (Mj : (D.obj j).Modules)
      (hMj : AlgebraicGeometry.SheafOfModules.IsInvertible
        (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property Mj),
      let _ := hMj
      Nonempty (tensorPower (D.obj j).sheaf.obj (D.obj j).ringCatSheaf.property Mj (n : ℤ) ≅
        (Scheme.Modules.pullback (D.map e)).obj L) := by
  obtain ⟨k, e, Mk, hMk, _, j, f, β, _⟩ :=
    exists_tensorPower_root_of_isLimit D c hc i L M n α
  let := hMk
  refine ⟨j, f ≫ e, (Scheme.Modules.pullback (D.map f)).obj Mk, inferInstance, ⟨?_⟩⟩
  exact β ≪≫ canIso (D.map f) (D.map e) (D.map (f ≫ e)) (D.map_comp f e).symm L

end Stacks.AlgebraicGeometry.ModuleLimits
