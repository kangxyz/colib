/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.FrameTransport
public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.GlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.NormIdealSheaf

/-!
# Simultaneous frames on a free affine chart of a finite norm

Both invertible modules are trivialized on one original affine chart.
The finite free algebra and the two frames are read on its actual pullback.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms
open Stacks.Ample

universe u

namespace AlgebraicGeometry.Scheme

/-- The same affine section module is free in the top sections of the
chosen scheme pullback. -/
theorem moduleFree_pullbackOpen_of_moduleFree_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    letI : Algebra Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) :=
      (pullback.snd f U.ι).appTop.hom.toAlgebra
    Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U) →
      Module.Free Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) := by
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) :=
    (pullback.snd f U.ι).appTop.hom.toAlgebra
  intro hfree
  let : Module.Free Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := hfree
  let i := pullbackRestrictIsoRestrict f U
  let eA := U.topIso.symm.commRingCatIsoToRingEquiv
  let eB := ((f ⁻¹ᵁ U).topIso.symm ≪≫ (asIso i.hom.appTop)).commRingCatIsoToRingEquiv
  have hf : U.topIso.inv ≫ (f ∣_ U).appTop = f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
    have h : (f ∣_ U).appTop = U.topIso.hom ≫ f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
      have he := f.resLE_app_top (U := U) (V := f ⁻¹ᵁ U) le_rfl
      change (f.resLE U (f ⁻¹ᵁ U) le_rfl).appTop = _ at he
      rw [Hom.resLE_eq_morphismRestrict, Hom.appLE_eq_app] at he
      exact he
    rw [h, Iso.inv_hom_id_assoc]
  have h : (f.app U ≫ (f ⁻¹ᵁ U).topIso.inv) ≫ i.hom.appTop =
      U.topIso.inv ≫ (pullback.snd f U.ι).appTop := by
    rw [← hf, Category.assoc, ← Hom.comp_appTop, pullbackRestrictIsoRestrict_hom_morphismRestrict]
  let : RingHomInvPair eA.toRingHom eA.symm.toRingHom := RingHomInvPair.of_ringEquiv eA
  let : RingHomInvPair eA.symm.toRingHom eA.toRingHom := RingHomInvPair.of_ringEquiv eA.symm
  let E : Γ(X, f ⁻¹ᵁ U) ≃ₛₗ[eA.toRingHom] Γ(pullback f U.ι, ⊤) :=
    { eB.toAddEquiv with
      map_smul' := fun a s ↦ by
        rw [Algebra.smul_def, Algebra.smul_def]
        change eB (algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U) a * s) =
          algebraMap Γ(U.toScheme, ⊤) Γ(pullback f U.ι, ⊤) (eA a) * eB s
        rw [map_mul]
        congr 1
        exact congrArg (fun k : Γ(Y, U) ⟶ Γ(pullback f U.ι, ⊤) ↦ k.hom a) h }
  exact Module.Free.of_equiv E

/-- The two invertible modules admit frames on the same free affine chart
containing the original target point. -/
theorem exists_freeAffineNormChart_frames {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteLocallyFree f] (L : X.Modules) [hL : IsInvertibleModule X L]
    (M : Y.Modules) [hM : IsInvertibleModule Y M] (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty ((Modules.pullback (pullback.fst f U.1.ι)).obj L ≅
        SheafOfModules.unit (pullback f U.1.ι).ringCatSheaf) ∧
      Nonempty ((Modules.pullback U.1.ι).obj M ≅ SheafOfModules.unit U.1.toScheme.ringCatSheaf) ∧
      letI : Algebra Γ(U.1.toScheme, ⊤) Γ(pullback f U.1.ι, ⊤) :=
        (pullback.snd f U.1.ι).appTop.hom.toAlgebra
      Module.Free Γ(U.1.toScheme, ⊤) Γ(pullback f U.1.ι, ⊤) := by
  let : IsFinite f := IsFiniteLocallyFree.isFinite f
  let : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 hL
  let : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).2 hM
  obtain ⟨V, hyV, ⟨eL⟩⟩ := Stacks.Divisors.hasTrivializingTargetCover_of_isFinite f L y
  obtain ⟨W, hyW, eM'⟩ := Stacks.Divisors.hasTrivializingTargetCover_of_isFinite (𝟙 Y) M y
  have eM : Nonempty (M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
    simpa only [Hom.id_preimage] using eM'
  obtain ⟨U, hyU, hU, hfree⟩ := Stacks.Norm.exists_affineOpens_mem_le_free f y (V ⊓ W) ⟨hyV, hyW⟩
  refine ⟨U, hyU, ?_, ?_, moduleFree_pullbackOpen_of_moduleFree_sections f U.1 hfree⟩
  · let j := (f ⁻¹ᵁ U.1).ι
    let v := pullbackRestrictIsoRestrict f U.1
    let e := ((Modules.restrictFunctorIsoPullback j).app L).symm ≪≫
      Stacks.SheafOfModules.restrictIsoUnitOfLE L (f.preimage_mono (hU.trans inf_le_left)) eL
    exact ⟨(Modules.pullbackCongr (pullbackRestrictIsoRestrict_hom_ι f U.1).symm).app L ≪≫
      ((Modules.pullbackComp v.hom j).app L).symm ≪≫ Modules.framePullback v.hom e⟩
  · exact ⟨((Modules.restrictFunctorIsoPullback U.1.ι).app M).symm ≪≫
      Stacks.SheafOfModules.restrictIsoUnitOfLE M (hU.trans inf_le_right) eM.some⟩

end AlgebraicGeometry.Scheme
