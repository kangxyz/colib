module

import Colib.AlgebraicGeometry.KTheory.PerfectQcqsScalarBoundary

open CategoryTheory AlgebraicGeometry Topology SSet TopologicalSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open CategoryTheory.Waldhausen.Fibration CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules
open scoped Simplicial Topology
noncomputable section
universe u v
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (n : ℕ)

example :
    (perfectOpenConnectingHom j n).comp
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) n) =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) :=
  perfectOpenConnectingHom_comp_scalarSelfTrack j r q hq n

example :
    (perfectOpenConnectingHom j 0).comp
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) 0) =
      (perfectAcyclicSupportedKEquiv j 0).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq 0) :=
  perfectOpenConnectingHom_comp_scalarSelfTrack j r q hq 0

example :
    (perfectOpenConnectingHom j n).comp
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) n) =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) :=
  perfectOpenConnectingHom_comp_scalarOriginalSelfTrack j r q hq n

example :
    (perfectOpenConnectingHom j 0).comp
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) 0) =
      (perfectAcyclicSupportedKEquiv j 0).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq 0) :=
  perfectOpenConnectingHom_comp_scalarOriginalSelfTrack j r q hq 0

example (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n) :
    perfectOpenConnectingHom j n
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) n a) =
      perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) :=
  perfectOpenConnectingHom_scalarSelfTrack j r q hq n a

example (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 0) :
    perfectOpenConnectingHom j 0
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) 0 a) =
      perfectAcyclicSupportedKEquiv j 0 (perfectOpenScalarConeKMap j r q hq 0 a) :=
  perfectOpenConnectingHom_scalarSelfTrack j r q hq 0 a

example (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n) :
    perfectOpenConnectingHom j n
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) n a) =
      perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) :=
  perfectOpenConnectingHom_scalarOriginalSelfTrack j r q hq n a

example (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 0) :
    perfectOpenConnectingHom j 0
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) 0 a) =
      perfectAcyclicSupportedKEquiv j 0 (perfectOpenScalarConeKMap j r q hq 0 a) :=
  perfectOpenConnectingHom_scalarOriginalSelfTrack j r q hq 0 a

example (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n) :
    ∃ p : GenLoop (Fin (n + 1))
      |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
      (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)),
      (⟦perfectScalarProjectionInputCube n p⟧ :
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n) = a :=
  perfectScalarProjectionInputCube_class_surjective X n a

example {G : Type v} [Monoid G]
    (f g : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n →* G)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
      (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)),
      f ⟦perfectScalarProjectionInputCube n p⟧ = g ⟦perfectScalarProjectionInputCube n p⟧) :
    f = g :=
  perfectScalarProjectionInputCube_hom_ext X n f g h

section GeneralUniverses
universe w w'
variable {C : Type v} [Category.{w} C] (V : Structure C)

example {Y : Sort w'} (f g : V.K n → Y)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|
      (subdivisionBasepoint V),
      f ⟦GenLoop.postcomp (separatedFirstDeloopingMap V)
        (separatedFirstDeloopingMap_basepoint V) p⟧ =
      g ⟦GenLoop.postcomp (separatedFirstDeloopingMap V)
        (separatedFirstDeloopingMap_basepoint V) p⟧) : f = g :=
  separatedFirstCube_funext V n f g h

end GeneralUniverses

section Qcqs

universe d

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  [HasDerivedCategory.{d} U.Modules]

-- The homomorphism form has the original positive cone sign on the actual qcqs boundary.
example :
    (perfectQcqsConnectingHom j n).comp
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace) (perfectFlatUnitHomotopy j q) n) =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) :=
  (perfectQcqsConnectingHom_comp_scalarUnitOperation j r q hq n).trans
    (perfectAcyclicSupportedKEquiv_scalarConeKMap j r q hq n).symm

-- In particular the original flat-unit operation on an arbitrary K-zero class is covered.
example (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 0) :
    perfectQcqsConnectingHom j 0
      (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
        (perfectFlatUnitHomotopy j q) 0 a) =
      perfectAcyclicSupportedKEquiv j 0 (perfectOpenScalarConeKMap j r q hq 0 a) :=
  DFunLike.congr_fun
    ((perfectQcqsConnectingHom_comp_scalarUnitOperation j r q hq 0).trans
      (perfectAcyclicSupportedKEquiv_scalarConeKMap j r q hq 0).symm) a

end Qcqs
