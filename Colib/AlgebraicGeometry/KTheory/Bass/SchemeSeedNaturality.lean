/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeNaturalSeed
public import Colib.Topology.Prespectrum.NullLoopNaturality

/-! # Original current-stage seed and normalized-stage compatibility

The whole original seed, independent loop times and literal association transports are
retained. This is the original equality of actual maps, not a stable-class replacement.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan
open GeometricSquareInterchange SquareConeStrength
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- A local whole-track intertwiner preserves the original all-scheme seed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeNaturalSeed.lean:33"
  "adaptation" "Original whole seed and fixed-order normalized transition square."]
theorem seed_square (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) :
    seed A ≫ (strictDiagramFunctor squareFunctor).map η = η ≫ seed B := by
  apply NatTrans.ext
  funext X
  change (((sourceTrack F A.homotopy X).postcomp
      (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (square X)))))
      |>.nullLoopMap (StrictSquare.sourceNullHomotopy
        (F.mapArrow.mapArrow.obj (square X)))) ≫
    parameterLoopingMap ((ConeTrack.map squareFunctor η).app X) = _
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (mappingConeInclusion (StrictSquare.comparison
        (G.mapArrow.mapArrow.obj (square X)))).map n
      ((η.app (laurent.op.obj X)).map n ((A.homotopy X).level n (r, x))) =
      (mappingConeInclusion (StrictSquare.comparison
        (G.mapArrow.mapArrow.obj (square X)))).map n
      ((B.homotopy X).level n (r, (η.app X).map n x))
    exact congrArg _ (congrArg (fun k => k.map n x) (hη X r)).symm
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    exact StrictSquare.sourceNullHomotopy_naturality_apply
      (diagramSquareMap η (square X)) n r x

end KTheory.Bass.SchemeNaturalSeed
