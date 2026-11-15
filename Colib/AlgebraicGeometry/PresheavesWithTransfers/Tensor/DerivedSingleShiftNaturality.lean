/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedConvolution

/-! # Naturality of the derived shift comparison for literal single complexes -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K

variable [HasDerivedCategory.{w} PST(k)]

/-- The degree comparison for literal singles commutes with the original coefficient map. -/
@[reassoc]
theorem singleDerivedMinusShiftIso_naturality {A B : PST(k)} (f : A ⟶ B) (n : ℤ) :
    (shiftFunctor (DerivedCategory.Minus PST(k)) (-n)).map ((singleDerivedMinus k 0).map f) ≫
        (singleDerivedMinusShiftIso B n).hom =
      (singleDerivedMinusShiftIso A n).hom ≫ (singleDerivedMinus k n).map f := by
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let S₀ := singleDerivedMinus k 0
  let Sₙ := singleDerivedMinus k n
  let s₀ := DerivedCategory.singleFunctorIsoCompQ PST(k) 0
  let sₙ := DerivedCategory.singleFunctorIsoCompQ PST(k) n
  let shiftSingle := ((DerivedCategory.singleFunctors PST(k)).shiftIso (-n) n 0 (by omega))
  let sh := shiftFunctor (DerivedCategory PST(k)) (-n)
  let a := S₀.map f
  let b := Sₙ.map f
  have h (P : PST(k)) : V.map (singleDerivedMinusShiftIso P n).hom =
      (V.commShiftIso (-n)).hom.app (S₀.obj P) ≫
        sh.map (s₀.inv.app P) ≫ shiftSingle.hom.app P ≫ sₙ.hom.app P := by
    unfold singleDerivedMinusShiftIso
    rw [Functor.preimageIso, Functor.map_preimage]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rfl
  apply V.map_injective
  simp only [V.map_comp, h, Category.assoc]
  have hV := (V.commShiftIso (-n)).hom.naturality_assoc a
    (sh.map (s₀.inv.app B) ≫ shiftSingle.hom.app B ≫ sₙ.hom.app B)
  change V.map ((shiftFunctor _ (-n)).map a) ≫
      (V.commShiftIso (-n)).hom.app (S₀.obj B) ≫
      sh.map (s₀.inv.app B) ≫ shiftSingle.hom.app B ≫ sₙ.hom.app B =
    (V.commShiftIso (-n)).hom.app (S₀.obj A) ≫ sh.map (V.map a) ≫
      sh.map (s₀.inv.app B) ≫ shiftSingle.hom.app B ≫ sₙ.hom.app B at hV
  rw [hV]
  have h₀ := s₀.inv.naturality f
  have hₙ := sₙ.hom.naturality f
  have hc := shiftSingle.hom.naturality f
  change V.map a ≫ s₀.inv.app B =
    s₀.inv.app A ≫ (DerivedCategory.singleFunctor PST(k) 0).map f at h₀
  change (DerivedCategory.singleFunctor PST(k) n).map f ≫ sₙ.hom.app B =
    sₙ.hom.app A ≫ V.map b at hₙ
  let S₀' := DerivedCategory.singleFunctor PST(k) 0
  let Sₙ' := DerivedCategory.singleFunctor PST(k) n
  have hs : sh.map (S₀'.map f) ≫ shiftSingle.hom.app B =
      shiftSingle.hom.app A ≫ Sₙ'.map f := hc
  rw [← sh.map_comp_assoc, h₀, sh.map_comp, Category.assoc]
  exact congrArg
    (fun x => (V.commShiftIso (-n)).hom.app (S₀.obj A) ≫ sh.map (s₀.inv.app A) ≫ x)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ sₙ.hom.app B) hs)).trans
      ((Category.assoc _ _ _).trans (congrArg (shiftSingle.hom.app A ≫ ·) hₙ)))

end AlgebraicGeometry.PresheafWithTransfers
