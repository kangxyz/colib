/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-! Original null-loop conjugation preserves proved unit and nullhomotopy comparisons. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/RelativeHomotopyConjugation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy

/-- Intertwining units and comparing original null tracks compares their actual based conjugates. -/
def conjugateNaturality {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (L : Homotopy f g) (U : Homotopy f f) (V : Homotopy g g)
    (N₀ : Homotopy f (zeroHom E F)) (N₁ : Homotopy g (zeroHom E F))
    (JU : (U.trans L).RelHomotopy (L.trans V))
    (JN : N₀.RelHomotopy (L.trans N₁)) :
    (U.conjugateToZero N₀).RelHomotopy (V.conjugateToZero N₁) := by
  let T := V.trans N₁
  have JU' : (U.trans (L.trans N₁)).RelHomotopy (L.trans T) :=
    (transAssoc U L N₁).symm.trans
      ((JU.hcomp (refl N₁)).trans (transAssoc L V N₁))
  have JC : (L.symm.trans (L.trans T)).RelHomotopy T :=
    (transAssoc L.symm L T).symm.trans
      (((reflSymmTrans L).symm.hcomp (refl T)).trans (reflTrans T))
  have J : ((L.trans N₁).symm.trans (U.trans (L.trans N₁))).RelHomotopy
      (N₁.symm.trans T) := by
    rw [Homotopy.symm_trans]
    exact (transAssoc N₁.symm L.symm (U.trans (L.trans N₁))).trans
      ((refl N₁.symm).hcomp (((refl L.symm).hcomp JU').trans JC))
  exact (JN.symmPath.hcomp ((refl U).hcomp JN)).trans J

end Topology.LoopPrespectrum.Homotopy.RelHomotopy

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/RelativeHomotopyConjugation.lean:18-36"
  "adaptation" "Proved unit and original-null comparisons preserve the original conjugated loop"]
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.conjugateNaturality
