/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# A genuine finite degree bound for the whole original Tor family

In the actual smooth-correspondence setting over an arbitrary field, each
original pair stalk has a finite regular-local Tor bound. The full finite
model has finitely many maximal ideals. Take the maximum of the original
bounds at those actual points, then use native localization detection of zero
modules. Every full finite coefficient module above that bound is zero.

This is module vanishing, not cancellation in an Euler characteristic or a
zero truncated infinite length. Raw stalk and localization lengths are used
throughout. No global smooth dimension, constant rank, quasi-compact smooth
ambient, geometric reducedness, or caller-supplied uniform bound is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g]

/-- At each actual finite-model point the original pair's actual local Tor bound kills
its sheaf stalk. The equality used here is before conversion to natural-number lengths. -/
theorem length_correspondenceRemainingFiniteTorSheaf_stalk_eq_zero_of_lt
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) (n : ℕ)
    (hn : correspondenceIncidenceTorDegreeBound k f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q)) < n) :
    Module.length ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
      ((correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) = 0 := by
  rw [length_correspondenceRemainingFiniteTorSheaf_stalk,
    length_correspondenceLeftExteriorTorSheaf_stalk]
  have hzero : Module.length
      (correspondenceIncidenceAmbientStalk f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceRemainingFiniteModelProjection f g h i z w v x q)))
      (correspondenceIncidenceAmbientTor f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceRemainingFiniteModelProjection f g h i z w v x q)) n) = 0 :=
    length_correspondenceIncidenceTor_eq_zero_of_lt k f g h z w _ n hn
  rw [hzero, zero_mul]

/-- The actual whole finite coefficient family vanishes beyond one finite bound, obtained
from the finitely many maximal source labels and native localization detection. -/
theorem exists_correspondenceRemainingFiniteTorModule_degreeBound [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    ∃ d : ℕ, ∀ n : ℕ, d < n →
      IsZero (correspondenceRemainingFiniteTorModule f g h i z w v x n) := by
  classical
  let T := correspondenceRemainingFiniteModel f g h i z w v x
  let B := correspondenceRemainingFiniteRing f g h i z w v x
  let M := correspondenceRemainingFiniteTorModule f g h i z w v x
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField k f g h)
  let := finite_maximalSpectrum_correspondenceRemainingFiniteRing f g h i z w v hz hw x
  letI := Fintype.ofFinite (MaximalSpectrum B)
  have hlocal (p : MaximalSpectrum B) : ∃ d : ℕ, ∀ n : ℕ, d < n →
      Subsingleton (LocalizedModule p.asIdeal.primeCompl (M n)) := by
    obtain ⟨⟨q, hq⟩, hprime⟩ := (isAffineOpen_top T).primeIdealOf_surjective p.toPrimeSpectrum
    refine ⟨correspondenceIncidenceTorDegreeBound k f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q)), ?_⟩
    intro n hn
    have hlen := length_localized_correspondenceRemainingFiniteTorModule
      f g h i z w v hz hw x q n
    rw [hprime] at hlen
    apply (Module.length_eq_zero_iff (R := Localization.AtPrime p.asIdeal)).mp
    exact hlen.trans
      (length_correspondenceRemainingFiniteTorSheaf_stalk_eq_zero_of_lt
        k f g h i z w v x q n hn)
  choose d hd using hlocal
  refine ⟨Finset.univ.sup d, fun n hn => ?_⟩
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply Module.subsingleton_of_localization_maximal (R := B)
    (fun p => LocalizedModule p.primeCompl (M n))
    (fun p => LocalizedModule.mkLinearMap p.primeCompl (M n))
  intro p hp
  exact hd ⟨p, hp⟩ n ((Finset.le_sup (Finset.mem_univ ⟨p, hp⟩)).trans_lt hn)

/-- In particular, nonzero original Tor degrees form a finite set for the actual entire
finite model. This statement does not discard higher-degree signs by cancellation. -/
theorem finite_nonzero_correspondenceRemainingFiniteTorModule [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    {n : ℕ | ¬IsZero (correspondenceRemainingFiniteTorModule f g h i z w v x n)}.Finite := by
  obtain ⟨d, hd⟩ := exists_correspondenceRemainingFiniteTorModule_degreeBound
    k f g h i z w v hz hw x
  refine (Set.finite_Iic d).subset ?_
  intro n hn
  exact le_of_not_gt fun hlt => hn (hd n hlt)

end Stacks.Chow
