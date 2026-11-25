/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopyPostcompReparam

/-! The original relative conjugation recipe retains exact pointwise postcomposition,
with the same associators, cancellation families and independent coordinates. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- The actual chosen conjugation family commutes pointwise with the supplied target map.
Every unit/null input and their supplied full comparisons are retained explicitly. -/
theorem Homotopy.RelHomotopy.conjugateNaturality_mapped
    {E F G : LoopPrespectrum.{u}} {f g : E ⟶ F} {f' g' : E ⟶ G}
    (L : Homotopy f g) (U : Homotopy f f) (V : Homotopy g g)
    (N₀ : Homotopy f (zeroHom E F)) (N₁ : Homotopy g (zeroHom E F))
    (JU : (U.trans L).RelHomotopy (L.trans V))
    (JN : N₀.RelHomotopy (L.trans N₁))
    (L' : Homotopy f' g') (U' : Homotopy f' f') (V' : Homotopy g' g')
    (N₀' : Homotopy f' (zeroHom E G)) (N₁' : Homotopy g' (zeroHom E G))
    (JU' : (U'.trans L').RelHomotopy (L'.trans V'))
    (JN' : N₀'.RelHomotopy (L'.trans N₁'))
    (j : F ⟶ G) (n : ℕ) (x : E.space n)
    (hL : L.MappedAt j n x L') (hU : U.MappedAt j n x U')
    (hV : V.MappedAt j n x V') (hN₁ : N₁.MappedAt j n x N₁')
    (hJU : JU.MappedAt j n x JU') (hJN : JN.MappedAt j n x JN') :
    (Homotopy.RelHomotopy.conjugateNaturality L U V N₀ N₁ JU JN).MappedAt j n x
      (Homotopy.RelHomotopy.conjugateNaturality L' U' V' N₀' N₁' JU' JN') := by
  have hT := hV.trans hN₁
  have hJU' := (hU.transAssoc hL hN₁).symm.trans
    ((hJU.hcomp hN₁.refl).trans (hL.transAssoc hV hN₁))
  have hJC := (hL.symm.transAssoc hL hT).symm.trans
    ((hL.reflSymmTrans.symm.hcomp hT.refl).trans hT.reflTrans)
  unfold Homotopy.RelHomotopy.conjugateNaturality
  apply Homotopy.RelHomotopy.MappedAt.trans
  · exact hJN.symmPath.hcomp (hU.refl.hcomp hJN)
  · apply Homotopy.RelHomotopy.MappedAt.transport
    · simp only [Homotopy.symm_trans]
    · rfl
    · simp only [Homotopy.symm_trans]
    · rfl
    · exact (hN₁.symm.transAssoc hL.symm (hU.trans (hL.trans hN₁))).trans
        (hN₁.symm.refl.hcomp ((hL.symm.refl.hcomp hJU').trans hJC))

end Topology.LoopPrespectrum
