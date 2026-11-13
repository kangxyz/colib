/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryBasicNull
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentNull
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullTwistedFiberComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputNullNaturality
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputMapComposition

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryBasicCurrent.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The actual auxiliary-to-basic current diagram

The original support-forget and union-to-basic Model maps induce the displayed
current telescope maps. Both original arrow squares and every time slice of
the selected-zero null are preserved before taking homotopy groups.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open ParameterLaurentTrack SchemeNaturalSeed NaturalTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The actual union-to-basic input preserves the original Laurent action. -/
theorem toBasic_equivariant : Equivariant (fiberAction f T) (supportedTrack f)
    (Functor.whiskerRight (toBasic f T) prespectrumFunctor) :=
  supportedMap_equivariant (vanishingPair f T)

/-- The original union-to-basic Model arrow acts on the actual current telescope. -/
def currentToBasic := currentInputMap (fiberAction f T) (supportedTrack f)
  (Functor.whiskerRight (toBasic f T) prespectrumFunctor) (toBasic_equivariant f T)

/-- The actual auxiliary ambient support is forgotten on its own current telescope. -/
def currentAmbientForget := currentInputMap (ambientAction T) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget T.ι) prespectrumFunctor) (forget_equivariant T.ι)

/-- The actual inverse-open support is forgotten on its own current telescope. -/
def currentOpenForget := currentInputMap (openAction f T) (ambientTrack P)
  (Functor.whiskerRight (ParameterModels.forget (inverseOpen f T).ι) prespectrumFunctor)
  (forget_equivariant (inverseOpen f T).ι)

/-- The original enlargement square remains literal on all current cylinders. -/
theorem currentEnlargement_basic_square :
    currentEnlargement f T ≫ currentAmbientForget T =
      currentToBasic f T ≫ ParameterFullCurrentNull.currentForget f := by
  let ρ := Functor.whiskerRight (ParameterModels.forget (unionOpen f T).ι) prespectrumFunctor
  have hleft := currentInputMap_comp_eq
    (fiberAction f T) (ambientAction T) (ambientTrack Q)
    (firstMap f T) (enlargement_equivariant f T)
    (Functor.whiskerRight (ParameterModels.forget T.ι) prespectrumFunctor)
    (forget_equivariant T.ι)
    ((enlargement_equivariant f T).comp (forget_equivariant T.ι))
    ρ (forget_equivariant (unionOpen f T).ι)
    (by dsimp only [firstMap, ρ]; rw [← Functor.whiskerRight_comp, enlargement_forget])
  have hright := currentInputMap_comp_eq
    (fiberAction f T) (supportedTrack f) (ambientTrack Q)
    (Functor.whiskerRight (toBasic f T) prespectrumFunctor) (toBasic_equivariant f T)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)
    ((toBasic_equivariant f T).comp (forget_equivariant f))
    ρ (forget_equivariant (unionOpen f T).ι)
    (by dsimp only [ρ]; rw [← Functor.whiskerRight_comp, toBasic_forget])
  exact hleft.trans hright.symm

/-- The original full-open restriction and auxiliary support-forget square agree strictly. -/
theorem currentRestriction_basic_square :
    currentRestriction f T ≫ currentOpenForget f T =
      currentAmbientForget T ≫ ParameterFullCurrentNull.currentOpen f := by
  have h : secondMap f T ≫
      Functor.whiskerRight (ParameterModels.forget (inverseOpen f T).ι) prespectrumFunctor =
    Functor.whiskerRight (ParameterModels.forget T.ι) prespectrumFunctor ≫
      ParameterFullCurrentNull.fullMap f := by
    dsimp only [secondMap, ParameterFullCurrentNull.fullMap]
    rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp,
      ← Functor.whiskerRight_comp, restriction_forget, fullRestriction_eq_ambientMap]
  exact (currentInputMap_comp_eq
    (ambientAction T) (openAction f T) (ambientTrack P)
    (secondMap f T) (restriction_equivariant f T)
    (Functor.whiskerRight (ParameterModels.forget (inverseOpen f T).ι) prespectrumFunctor)
    (forget_equivariant (inverseOpen f T).ι)
    ((restriction_equivariant f T).comp (forget_equivariant (inverseOpen f T).ι))
    _ ((forget_equivariant T.ι).comp (ParameterFullCurrentNull.fullMap_equivariant f)) h).trans
      (currentInputMap_comp (ambientAction T) (ambientTrack Q) (ambientTrack P)
        (Functor.whiskerRight (ParameterModels.forget T.ι) prespectrumFunctor)
        (forget_equivariant T.ι) (ParameterFullCurrentNull.fullMap f)
        (ParameterFullCurrentNull.fullMap_equivariant f)
        ((forget_equivariant T.ι).comp (ParameterFullCurrentNull.fullMap_equivariant f))).symm

/-- The entire original auxiliary null retains the basic null at its unchanged time. -/
theorem currentNull_basic_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (fiberAction f T)).obj X).space n) :
    ((currentOpenForget f T).app X).map n
        (((currentNull f T).homotopy X).level n (r, x)) =
      ((ParameterFullCurrentNull.currentNull f).homotopy X).level n
        (r, ((currentToBasic f T).app X).map n x) :=
  currentInputNull_naturality
    (fiberAction f T) (ambientAction T) (openAction f T)
    (supportedTrack f) (ambientTrack Q) (ambientTrack P)
    (firstMap f T) (secondMap f T)
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor)
    (ParameterFullCurrentNull.fullMap f)
    (enlargement_equivariant f T) (restriction_equivariant f T)
    (forget_equivariant f) (ParameterFullCurrentNull.fullMap_equivariant f)
    (fullNull f T) (ParameterFullCurrentNull.fullNull f)
    (timeSlice_equivariant f T) (ParameterFullCurrentNull.timeSlice_equivariant f)
    (Functor.whiskerRight (toBasic f T) prespectrumFunctor)
    (Functor.whiskerRight (ParameterModels.forget (inverseOpen f T).ι) prespectrumFunctor)
    (toBasic_equivariant f T) (forget_equivariant (inverseOpen f T).ι)
    (fullNull_basic_square f T) X n r x

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
