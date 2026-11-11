/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeNaturalSeed
public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeed
public import Colib.Topology.Prespectrum.StrictSquareSeedNaturality

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
universe u w
namespace KTheory.Bass.SchemeCoefficientSeedNaturality
open NaturalTrack GeometricSeedCospan
variable {R : CommRingCat.{u}} {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}
    {G : Under R ⥤ LoopPrespectrum.{w}}
    (A : Track laurent.op coefficient F) (B : LaurentSeed.Track G)
    (X : Scheme.{u}ᵒᵖ) (a : Under R)

/-- Only the original coefficient diagonal endpoints are changed to their square presentation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCoefficientSeedNaturality.lean:35"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def coefficientTrack :
    Homotopy ((LaurentSeed.square G a).left.hom ≫ (LaurentSeed.square G a).hom.right)
      ((LaurentSeed.square G a).left.hom ≫ (LaurentSeed.square G a).hom.right) :=
  (B.homotopy a).cast (LaurentSeed.square_source G a).symm
    (LaurentSeed.square_source G a).symm

/-- The original Scheme seed is the strict-square seed with its original endpoint cast. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCoefficientSeedNaturality.lean:42"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem scheme_seed_eq :
    (SchemeNaturalSeed.seed A).app X =
      ((sourceTrack F A.homotopy X).postcomp
        (mappingConeInclusion (StrictSquare.comparison
          (F.mapArrow.mapArrow.obj (square X))))).nullLoopMap
        (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (square X))) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext t
  rfl

/-- The original coefficient seed has the same whole word after its diagonal endpoint cast. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCoefficientSeedNaturality.lean:57"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem coefficient_seed_eq :
    B.seed.app a =
      ((coefficientTrack B a).postcomp
        (mappingConeInclusion (StrictSquare.comparison (LaurentSeed.square G a)))).nullLoopMap
        (StrictSquare.sourceNullHomotopy (LaurentSeed.square G a)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext t
  rfl

/-- A whole scalar square gives the original Scheme-to-coefficient seed square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeCoefficientSeedNaturality.lean:71"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem seed_naturality
    (e : F.mapArrow.mapArrow.obj (square X) ⟶ LaurentSeed.square G a)
    (hU : ∀ n r x, e.right.right.map n ((A.homotopy X).level n (r, x)) =
      (B.homotopy a).level n (r, e.left.left.map n x)) :
    (SchemeNaturalSeed.seed A).app X ≫ strictSquareLoopedConeFunctor.map e =
      e.left.left ≫ B.seed.app a := by
  rw [scheme_seed_eq A X, coefficient_seed_eq B a]
  exact StrictSquare.sourceSeed_naturality e (sourceTrack F A.homotopy X)
    (coefficientTrack B a) hU

end KTheory.Bass.SchemeCoefficientSeedNaturality

