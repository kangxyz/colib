/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotientBoundary

/-!
The boundary may be the spectrum of an arbitrary commutative ring. No reducedness,
flatness, integrality or Noetherian hypothesis is available in these examples.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u})
  (i : Spec (CommRingCat.of R) ⟶ X) (L N : X.Modules)
  [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
  (b : N.sections)
  (e : (pullback i).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)
  (eN : (pullback i).obj N ≅ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)
  (a : Γ(tensorObj L N, ⊤))
  (ha : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
    (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(Spec (CommRingCat.of R), ⊤)))
  (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) =
    (1 : Γ(Spec (CommRingCat.of R), ⊤)))

example : i ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b = ⊤ :=
  preimage_nonvanishingOpen_eq_top_of_boundary_frame i N b eN hb

example : Hom.app e.hom ⊤ (boundaryRegularTensorQuotient i L N b eN hb a) =
    (1 : Γ(Spec (CommRingCat.of R), ⊤)) :=
  frame_boundaryRegularTensorQuotient_eq_one i L N b e eN a ha hb

#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorFrame_tensorSection_of_right_one
#print axioms AlgebraicGeometry.Scheme.Modules.preimage_nonvanishingOpen_eq_top_of_boundary_frame
#print axioms AlgebraicGeometry.Scheme.Modules.frame_boundaryRegularTensorQuotient_eq_one
