/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleStalkIdeal
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstHomologyEuler
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.RingTheory.HilbertSamuel.Defs

/-!
# The three actual sixfold supports meet only at the generic incidence point

The two modules are the quotients by the literal Y and Z diagonal stalk ideals.
The third is the already defined full exterior-support stalk with its original
sixfold scalar action. Their support intersection is the closed point at every
original generic triple-incidence label. This follows from the actual three-ideal
quotient, whose full local ring is Artinian, not from a reduced replacement.

The sixfold ambient is smooth over the arbitrary base field when the four original
factors are smooth. Native Stacks 056S and 02IT supply regular local rings. The
local dimension is a finite natural number. These facts discharge the geometric
hypotheses of native local triple-Tor associativity (0B1L); no cycle or associativity
comparison is defined in this lower module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "V" => correspondenceSixfoldAmbient f g h i
local notation3 (prettyPrint := false) "j" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v

/-- The first original diagonal quotient in the unchanged sixfold local ring. -/
abbrev correspondenceTripleIncidenceFirstDiagonalQuotient
    (x : correspondenceTripleIncidence f g h i z w v) :
    ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :=
  ModuleCat.of (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
    (correspondenceTripleIncidenceAmbientStalk f g h i z w v x ⧸
      IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker (j x))

/-- The second original diagonal quotient in the same sixfold local ring. -/
abbrev correspondenceTripleIncidenceSecondDiagonalQuotient
    (x : correspondenceTripleIncidence f g h i z w v) :
    ModuleCat (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :=
  ModuleCat.of (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
    (correspondenceTripleIncidenceAmbientStalk f g h i z w v x ⧸
      IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker (j x))

/-- The original three-ideal sum has maximal radical at every generic triple point. -/
theorem radical_correspondenceTripleIncidenceThreeStalkIdeals
    [IsSeparated g] [IsSeparated h] [IsLocallyNoetherian V]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    (correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v x.1).radical =
      IsLocalRing.maximalIdeal (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1) := by
  have : IsLocallyNoetherian (correspondenceTripleIncidence f g h i z w v) :=
    LocallyOfFiniteType.isLocallyNoetherian j
  have := generic_stalk_artinian x
  rw [← correspondenceTripleIncidenceSixfoldInclusion_stalkMap_ker,
    RingHom.ker_eq_comap_bot, ← Ideal.comap_radical,
    ← IsArtinianRing.jacobson_eq_radical, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
    IsLocalRing.maximalIdeal_comap]

/-- The two literal diagonal quotients and full exterior module have only closed-point
common support at an original generic triple-incidence label. -/
theorem support_correspondenceTripleIncidence_threeModules
    [IsSeparated g] [IsSeparated h] [IsLocallyNoetherian V]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    Module.support (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceFirstDiagonalQuotient f g h i z w v x.1) ∩
      Module.support (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1) ∩
      Module.support (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x.1) ⊆
          {IsLocalRing.closedPoint
            (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)} := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x.1
  rintro q ⟨⟨hY, hM⟩, hZ⟩
  have hY' := Module.mem_support_iff_of_finite.mp hY
  have hZ' := Module.mem_support_iff_of_finite.mp hZ
  change Module.annihilator A (A ⧸
    IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker (j x.1)) ≤ _ at hY'
  change Module.annihilator A (A ⧸
    IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker (j x.1)) ≤ _ at hZ'
  rw [Ideal.annihilator_quotient] at hY' hZ'
  have hM' := Module.mem_support_iff_of_finite.mp hM
  rw [correspondenceTripleIncidenceSupportStalkModule_annihilator] at hM'
  have hsum : correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v x.1 ≤
      q.asIdeal := sup_le hY' (sup_le hZ' hM')
  have hmax : IsLocalRing.maximalIdeal A ≤ q.asIdeal := by
    rw [← radical_correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v x]
    exact q.isPrime.radical_le_iff.mpr hsum
  exact Set.mem_singleton_iff.mpr
    (PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) hmax))

section Field

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))

/-- The original sixfold ambient structure morphism, retaining the rightmost base map. -/
abbrev correspondenceSixfoldAmbientToField :
    correspondenceSixfoldAmbient f g h i ⟶ Spec (.of k) :=
  pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) ≫
    pullback.fst h i ≫ h

instance smooth_correspondenceSixfoldAmbientToField
    [Smooth f] [Smooth g] [Smooth h] [Smooth i] :
    Smooth (correspondenceSixfoldAmbientToField k f g h i) := by
  dsimp only [correspondenceSixfoldAmbientToField, correspondenceAmbientTarget]
  infer_instance

/-- Smooth original factors give regular actual sixfold local rings over any field. -/
theorem isRegularLocalRing_correspondenceSixfoldAmbient_stalk
    [Smooth f] [Smooth g] [Smooth h] [Smooth i]
    (p : correspondenceSixfoldAmbient f g h i) :
    IsRegularLocalRing ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p) := by
  have hcriterion : IsRegular (correspondenceSixfoldAmbient f g h i) ↔
      IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i) ∧
        ∀ x : correspondenceSixfoldAmbient f g h i,
          IsRegularLocalRing ((correspondenceSixfoldAmbient f g h i).presheaf.stalk x) :=
    (isRegular_tfae (correspondenceSixfoldAmbient f g h i)).out 1 2
  exact (hcriterion.mp
    (isRegular_of_smooth_over_field (correspondenceSixfoldAmbientToField k f g h i))).2 p

variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The finite local dimension of the same actual sixfold stalk. -/
def correspondenceTripleIncidenceTorDegreeBound
    (x : correspondenceTripleIncidence f g h i z w v) : ℕ :=
  ((ringKrullDim (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)).unbotD 0).toNat

/-- The local bound equals the full actual ambient Krull dimension. -/
theorem ringKrullDim_eq_correspondenceTripleIncidenceTorDegreeBound
    [Smooth f] [Smooth g] [Smooth h] [Smooth i]
    (x : correspondenceTripleIncidence f g h i z w v) :
    ringKrullDim (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) =
      (correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x : WithBot ℕ∞) := by
  have := isRegularLocalRing_correspondenceSixfoldAmbient_stalk k f g h i
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x)
  exact eq_natCast_unbotD_toNat ringKrullDim_ne_bot ringKrullDim_ne_top

end Field

end Stacks.Chow
