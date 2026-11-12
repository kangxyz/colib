/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # The actual retained source-target map

These unchanged low-level declarations were extracted from
`PolynomialEndpointCorrespondence` and `RetainedSourceEndpointCycles`.
They require neither polynomial endpoint cycles nor correspondence composition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- The original curve source-target map. -/
def retainedCurveMap {k : Type u} [Field k] {X C V Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (h : Y ⟶ Spec (.of k)) (q : C ⟶ X)
    (j : V ⟶ C) (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ h) : V ⟶ pullback p h :=
  pullback.lift (j ≫ q) g hg

/-- An actual open subscheme of the original Noetherian curve is Noetherian. -/
theorem retainedCurve_isNoetherian {C V : Scheme.{u}} [IsNoetherian C]
    (j : V ⟶ C) [IsOpenImmersion j] : IsNoetherian V := by
  let : NoetherianSpace V := j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian j
  exact {}

end AlgebraicGeometry.PrincipalFamilyUnitOpen
