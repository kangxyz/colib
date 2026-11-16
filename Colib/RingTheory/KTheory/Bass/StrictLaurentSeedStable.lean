/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Bass.StrictLaurentSeed
public import Colib.Topology.Prespectrum.SelfTrackStableNullEvaluation

/-!
# Stable factorization of the original strict Laurent seed

The existing Laurent track seed is evaluated using its unchanged strict-square source null
and cone inclusion. The integer-graded factorization retains the exact parameter-loop shift,
alternating sign and target tail. No comparison with a different geometric source null or
with a supported K-theory cofiber is asserted.

Source: `Quillen/KTheory/Bass/StrictLaurentSeedStable.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum CommRingCat.PolynomialLaurent
universe u w
namespace KTheory.Bass.LaurentSeed
variable {R : CommRingCat.{u}} {F : Under R ⥤ LoopPrespectrum.{w}} (A : Track F)

/-- The existing strict seed factors through its original Laurent track and cone inclusion. -/
theorem Track.seedMap_stableHomotopy (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map (A.seedMap a) ≫
        (parameterStableHomotopyIso (cone F a) d).hom =
      (A.homotopy a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeInclusion (StrictSquare.comparison (square F a))) :=
  (A.homotopy a).nullLoopMap_stableHomotopy_postcomp
    (mappingConeInclusion (StrictSquare.comparison (square F a))) (sourceNull F a) d

/-- The same exact inverse shift gives the unchanged original strict seed map itself. -/
theorem Track.seedMap_stableHomotopy_eq (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map (A.seedMap a) =
      (A.homotopy a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeInclusion (StrictSquare.comparison (square F a))) ≫
            (parameterStableHomotopyIso (cone F a) d).inv := by
  apply (cancel_mono (parameterStableHomotopyIso (cone F a) d).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    A.seedMap_stableHomotopy a d

/-- Every original strict seed stage retains its sign, exact degree shift and final tail. -/
theorem Track.seedMap_stableHomotopy_ι (a : Under R) (d : ℤ) (n : ℕ) :
    stableHomotopyι (F.obj a) d n ≫ (stableHomotopyFunctor d).map (A.seedMap a) ≫
        (parameterStableHomotopyIso (cone F a) d).hom =
      ((-1 : ℤ) ^ n • (A.homotopy a).stableStageOperation d n) ≫
        (shiftedStableReindexIso (F.obj ((laurentUnderFunctor R).obj a)) d n).hom ≫
          stableHomotopyι (F.obj ((laurentUnderFunctor R).obj a)) (d + 1)
            (parameterStableOffset d + n) ≫
              (stableHomotopyFunctor (d + 1)).map
                (mappingConeInclusion (StrictSquare.comparison (square F a))) := by
  rw [A.seedMap_stableHomotopy, ← Category.assoc, Homotopy.stableOperation_ι]
  simp only [Category.assoc]


/-- A supplied natural seed has the stable cone factorization of a specified Laurent track.
The supplied seed, actual cone inclusion and parameter-loop shift all remain explicit data. -/
abbrev Track.SeedStableFactorization (A : Track F)
    (seed : F ⟶ (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj F)
    (a : Under R) (d : ℤ) : Prop :=
  (stableHomotopyFunctor d).map (seed.app a) ≫
      (parameterStableHomotopyIso (cone F a) d).hom =
    (A.homotopy a).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (mappingConeInclusion (StrictSquare.comparison (square F a)))

/-- The exact inverse-shift form of the same stable factorization for the supplied seed. -/
abbrev Track.SeedStableFormula (A : Track F)
    (seed : F ⟶ (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj F)
    (a : Under R) (d : ℤ) : Prop :=
  (stableHomotopyFunctor d).map (seed.app a) =
    (A.homotopy a).stableOperation d ≫
      (stableHomotopyFunctor (d + 1)).map
        (mappingConeInclusion (StrictSquare.comparison (square F a))) ≫
          (parameterStableHomotopyIso (cone F a) d).inv

/-- The same actual parameter-loop isomorphism converts the two factorization forms. -/
theorem Track.seedStableFactorization_iff_seedStableFormula (A : Track F)
    (seed : F ⟶ (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj F)
    (a : Under R) (d : ℤ) :
    A.SeedStableFactorization seed a d ↔ A.SeedStableFormula seed a d := by
  simpa only [Track.SeedStableFactorization, Track.SeedStableFormula, Category.assoc] using
    (Iso.eq_comp_inv (parameterStableHomotopyIso (cone F a) d)
      (f := (A.homotopy a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeInclusion (StrictSquare.comparison (square F a))))
      (g := (stableHomotopyFunctor d).map (seed.app a))).symm

/-- The unchanged track seed has its original stable cone factorization. -/
theorem Track.seed_hasStableFactorization (A : Track F) (a : Under R) (d : ℤ) :
    A.SeedStableFactorization A.seed a d :=
  A.seedMap_stableHomotopy a d

/-- The unchanged track seed has the same exact inverse-shift formula. -/
theorem Track.seed_hasStableFormula (A : Track F) (a : Under R) (d : ℤ) :
    A.SeedStableFormula A.seed a d :=
  (A.seedStableFactorization_iff_seedStableFormula A.seed a d).mp
    (A.seed_hasStableFactorization a d)

end KTheory.Bass.LaurentSeed
