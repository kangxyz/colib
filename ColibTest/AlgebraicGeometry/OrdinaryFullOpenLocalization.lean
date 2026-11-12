module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFullOpenBassLocalization
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
example : DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedBassTelescopeForget f)
    (boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f) :=
  boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f
example (a : Under R) :
    (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a =
      mappingConeDesc ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a) :=
  boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_eq_desc f a
variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
example (a : Under R) :
    IsStableEquivalence (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a) :=
  boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a

omit [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] in
example (a : Under R) :
    (stableHomotopyFunctor ((-2 : ℤ) + 1)).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a) ≫
      stableFiberConnecting ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        (-2) =
    stableMappingConeConnecting ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
      (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a)
        (-2) ≫
        (stableHomotopyFunctor (-2)).map
          (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a) :=
  boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenConeMap_connecting f a (-2)
