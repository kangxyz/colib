/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeedStable
public import Colib.KTheory.Bass.TwoChartStableSequence
public import Colib.KTheory.Bass.TwoChart
public import Colib.Topology.Prespectrum.SelfTrackStableNaturality

/-!
# Original Laurent unit quotients and the genuine spectral Bass row

A coefficient-natural whole Laurent track gives its actual stable operation and its original
chart quotient as natural transformations. The original seed factors through that quotient and
the unchanged spectral Bass left map, including the original signed inverse parameter shift.
When the seed is invertible, the genuine spectral short exact row first supplies monicity of
the Bass left map; the seed factorization then supplies epicity. Thus both original factors are
invertible, and original chart middle exactness follows. No geometric boundary identification
or replacement of the original Laurent quotient is used.

Source: `Quillen/KTheory/Bass/StrictLaurentUnitQuotient.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
open CommRingCat.PolynomialLaurent KTheory.Bass.TwoChartStable
universe u w
namespace KTheory.Bass.LaurentSeed
variable {R : CommRingCat.{u}} {F : Under R ⥤ LoopPrespectrum.{w}} (A : Track F)

private theorem stableOperation_cast {E B : LoopPrespectrum.{w}} {f g : E ⟶ B}
    (H : Homotopy f f) (h : f = g) (d : ℤ) :
    (H.cast h h).stableOperation d = H.stableOperation d := by
  subst g
  rfl

/-- The unchanged whole coefficient track induces the original stable naturality square. -/
@[reassoc]
theorem Track.stableOperation_naturality {a b : Under R} (g : a ⟶ b) (d : ℤ) :
    (stableHomotopyFunctor d).map (F.map g) ≫ (A.homotopy b).stableOperation d =
      (A.homotopy a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map (F.map ((laurentUnderFunctor R).map g)) := by
  have h : F.map ((laurentUnderCoefficient R).app a) ≫
      F.map ((laurentUnderFunctor R).map g) =
    F.map g ≫ F.map ((laurentUnderCoefficient R).app b) := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map ((laurentUnderCoefficient R).naturality g).symm
  have he : ((A.homotopy a).postcomp
      (F.map ((laurentUnderFunctor R).map g))).cast h h =
      (A.homotopy b).precomp (F.map g) := by
    apply Topology.LoopPrespectrum.Homotopy.ext
    funext n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact A.naturality g n t x
  have ho := congrArg (fun H => H.stableOperation d) he
  rw [stableOperation_cast, Homotopy.stableOperation_postcomp,
    Homotopy.stableOperation_precomp] at ho
  exact ho.symm

/-- The original degree-raising Laurent operation is natural in every coefficient map. -/
def Track.stableOperationNatTrans (d : ℤ) :
    F ⋙ stableHomotopyFunctor d ⟶
      laurentUnderFunctor R ⋙ (F ⋙ stableHomotopyFunctor (d + 1)) where
  app a := (A.homotopy a).stableOperation d
  naturality _ _ g := A.stableOperation_naturality g d

/-- The actual forward track followed by the original categorical Laurent quotient. -/
def Track.stableUnitQuotient (d : ℤ) :
    F ⋙ stableHomotopyFunctor d ⟶
      KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
        (F ⋙ stableHomotopyFunctor (d + 1)) :=
  A.stableOperationNatTrans d ≫
    KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (F ⋙ stableHomotopyFunctor (d + 1))

/-- The natural quotient uses exactly the original spectral chart cokernel projection. -/
theorem Track.stableUnitQuotient_app (a : Under R) (d : ℤ) :
    (A.stableUnitQuotient d).app a =
      (A.homotopy a).stableOperation d ≫
        cokernel.π (chartDifference (square F a) (d + 1)) := rfl

/-- The original seed equals the actual unit quotient followed by the genuine spectral left map.
-/
@[reassoc]
theorem Track.stableUnitQuotient_bassLeft (a : Under R)
    (hS : SpectralConditions (square F a)) (d : ℤ) :
    (A.stableUnitQuotient d).app a ≫ bassLeft (square F a) hS d =
      (stableHomotopyFunctor d).map (A.seedMap a) := by
  rw [A.stableUnitQuotient_app, Category.assoc, bassLeft_π]
  exact (A.seedMap_stableHomotopy_eq a d).symm

/-- Genuine spectral monicity and the invertible original seed force the Bass left map to be
invertible. Epicity is obtained from the original factorization, not assumed. -/
theorem Track.bassLeft_isIso_of_seed (a : Under R)
    (hS : SpectralConditions (square F a)) (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (A.seedMap a))] :
    IsIso (bassLeft (square F a) hS d) := by
  let : Mono (bassLeft (square F a) hS d) :=
    (bassSequence_shortExact (square F a) hS d).mono_f
  let : Epi (bassLeft (square F a) hS d) :=
    epi_of_epi_fac (A.stableUnitQuotient_bassLeft a hS d)
  exact isIso_of_mono_of_epi _

/-- The original stable unit quotient is invertible once the original seed is invertible. -/
theorem Track.stableUnitQuotient_isIso_of_seed (a : Under R)
    (hS : SpectralConditions (square F a)) (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (A.seedMap a))] :
    IsIso ((A.stableUnitQuotient d).app a) := by
  let := A.bassLeft_isIso_of_seed a hS d
  rw [← isIso_comp_right_iff _ (bassLeft (square F a) hS d),
    A.stableUnitQuotient_bassLeft]
  infer_instance

/-- The original chart complex is exact as a consequence of the genuine row and seed isomorphism.
-/
theorem Track.chart_exact_of_seed (a : Under R)
    (hS : SpectralConditions (square F a)) (d : ℤ)
    [IsIso ((stableHomotopyFunctor d).map (A.seedMap a))] :
    Function.Exact (strictOverlap (square F a) d) (chartDifference (square F a) d) := by
  have hz : IsZero (bassRightGroup (square F a) d) :=
    (bassSequence_shortExact (square F a) hS d).isIso_f_iff.mp
      (A.bassLeft_isIso_of_seed a hS d)
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    ((chartComplex (square F a) d).exact_iff_isZero_homology.mpr
      (hz.of_iso (chartHomologyRightIso (square F a) d)))

/-- Original chart middle exactness and invertibility of the forward quotient imply
invertibility of the literal seed, with its original parameter shift. -/
theorem Track.seed_isIso_of_chart_exact_of_stableUnitQuotient (a : Under R)
    (hS : SpectralConditions (square F a)) (d : ℤ)
    (hChart : Function.Exact (strictOverlap (square F a) d)
      (chartDifference (square F a) d))
    [IsIso ((A.stableUnitQuotient d).app a)] :
    IsIso ((stableHomotopyFunctor d).map (A.seedMap a)) := by
  let : IsIso (bassLeft (square F a) hS d) :=
    (bassSequence_shortExact (square F a) hS d).isIso_f_iff.mpr
      (bassRightGroup_isZero_of_chart_exact (square F a) d hChart)
  rw [← A.stableUnitQuotient_bassLeft a hS d]
  infer_instance

end KTheory.Bass.LaurentSeed
