/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy

/-!
# Canonical rebasing and a preserved chosen zero

If an exact functor already preserves the chosen zero, its canonically rebased map has
an actual coherent homotopy to its original prespectrum map. The homotopy is induced by
the existing rebase isomorphism; no strict equality of normalized functors is asserted.

This is a direct application of the original weak-transformation homotopy in Quillen
`Waldhausen/SConstruction/Iterated/PrespectrumHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u v

namespace CategoryTheory.Waldhausen.IteratedS

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The canonical zero-rebased map coherently agrees with the original zero-preserving map. -/
def exactOriginalPrespectrumMapChosenZeroHomotopy (h0 : F.obj W.zero = V.zero) :
    LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W V hF)
      (originalPrespectrumMap W V hF h0) :=
  originalPrespectrumTransformationHomotopy W V hF.rebase hF
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) h0
    (CategoryTheory.rebaseFunctorIso F W.zero V.zero
      ((hF.zero W.isZero).iso V.isZero)).inv
    (fun _ ↦ V.weq_iso _ inferInstance)

end CategoryTheory.Waldhausen.IteratedS
