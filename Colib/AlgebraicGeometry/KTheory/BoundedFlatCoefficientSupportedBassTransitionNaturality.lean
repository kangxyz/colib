/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTower
public import Colib.Topology.Prespectrum.ConeDescNaturality

/-!
# Naturality of the supported cone descent under the original Bass transition

The actual supported and ambient transitions give an arrow square. Its cone map
preserves the chosen localization null and hence the actual descent to the open row.

Source: `CoefficientSupportedConnectiveInvertibility.lean` in
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The actual original supported and ambient seed transitions form their unchanged arrow square.
-/
def boundedAboveFlatCoefficientSupportedBassTransitionSquare (i : ℕ) (a : Under R) :
    Arrow.mk ((boundedAboveFlatCoefficientSupportedBassForget f i).app a) ⟶
      Arrow.mk ((boundedAboveFlatCoefficientSupportedBassForget f (i + 1)).app a) :=
  Arrow.homMk ((boundedAboveFlatCoefficientSupportedBassTransition f i).app a)
    ((boundedAboveFlatCoefficientAmbientBassTransition Q i).app a)
    (NatTrans.congr_app (boundedAboveFlatCoefficientSupportedBassForget_transition f i) a).symm

/-- Every prescribed localization-null time gives literal transition naturality of cone descent.
-/
theorem boundedAboveFlatCoefficientSupportedBassOpenConeMap_transition (i : ℕ) (a : Under R) :
    mappingConeMap (boundedAboveFlatCoefficientSupportedBassTransitionSquare f i a) ≫
        (boundedAboveFlatCoefficientSupportedBassOpenConeMap f (i + 1)).app a =
      (boundedAboveFlatCoefficientSupportedBassOpenConeMap f i).app a ≫
        (boundedAboveFlatCoefficientOpenBassTransition f i).app a := by
  apply mappingConeDesc_naturality (boundedAboveFlatCoefficientSupportedBassTransitionSquare f i a)
    ((boundedAboveFlatCoefficientAmbientBassOpen f i).app a)
    ((boundedAboveFlatCoefficientAmbientBassOpen f (i + 1)).app a)
    ((boundedAboveFlatCoefficientOpenBassTransition f i).app a)
    ((boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a)
    ((boundedAboveFlatCoefficientSupportedBassOpenNull f (i + 1)).homotopy a)
  · exact (NatTrans.congr_app (boundedAboveFlatCoefficientAmbientBassOpen_transition f i) a).symm
  · exact boundedAboveFlatCoefficientSupportedBassOpenNull_transition f i a

end AlgebraicGeometry.Scheme.Modules
