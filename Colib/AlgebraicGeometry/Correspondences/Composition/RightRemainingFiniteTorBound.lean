/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# A genuine finite degree bound for the whole right G,H Tor family

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
  [Smooth g] [Smooth h] [Smooth i] [IsSeparated h]

/-- At each actual finite-model point the original pair's actual local Tor bound kills
its sheaf stalk. The equality used here is before conversion to natural-number lengths. -/
theorem length_correspondenceRightRemainingFiniteTorSheaf_stalk_eq_zero_of_lt
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) (n : ℕ)
    (hn : correspondenceIncidenceTorDegreeBound k g h i w v
      (correspondenceRightExteriorProjection f g h i z w v
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)) < n) :
    Module.length ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
      ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) = 0 := by
  let : Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g) := inferInstance
  rw [length_correspondenceRightRemainingFiniteTorSheaf_stalk,
    length_correspondenceRightExteriorTorSheaf_stalk]
  have hzero : Module.length
      (correspondenceIncidenceAmbientStalk g h i w v
        (correspondenceRightExteriorProjection f g h i z w v
          (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)))
      (correspondenceIncidenceAmbientTor g h i w v
        (correspondenceRightExteriorProjection f g h i z w v
          (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)) n) = 0 :=
    length_correspondenceIncidenceTor_eq_zero_of_lt k g h i w v _ n hn
  rw [hzero, zero_mul]

/-- The actual whole finite coefficient family vanishes beyond one finite bound, obtained
from the finitely many maximal source labels and native localization detection. -/
theorem exists_correspondenceRightRemainingFiniteTorModule_degreeBound [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    ∃ d : ℕ, ∀ n : ℕ, d < n →
      IsZero (correspondenceRightRemainingFiniteTorModule f g h i z w v x n) := by
  classical
  let T := correspondenceRightRemainingFiniteModel f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x
  let := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient g h i) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField k g h i)
  let := finite_maximalSpectrum_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x
  let := Fintype.ofFinite (MaximalSpectrum B)
  have hlocal (p : MaximalSpectrum B) : ∃ d : ℕ, ∀ n : ℕ, d < n →
      Subsingleton (LocalizedModule p.asIdeal.primeCompl (M n)) := by
    obtain ⟨⟨q, hq⟩, hprime⟩ := (isAffineOpen_top T).primeIdealOf_surjective p.toPrimeSpectrum
    refine ⟨correspondenceIncidenceTorDegreeBound k g h i w v
      (correspondenceRightExteriorProjection f g h i z w v
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)), ?_⟩
    intro n hn
    have hlen := length_localized_correspondenceRightRemainingFiniteTorModule
      f g h i z w v hw hv x q n
    rw [hprime] at hlen
    apply (Module.length_eq_zero_iff (R := Localization.AtPrime p.asIdeal)).mp
    exact hlen.trans
      (length_correspondenceRightRemainingFiniteTorSheaf_stalk_eq_zero_of_lt
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
theorem finite_nonzero_correspondenceRightRemainingFiniteTorModule [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    {n : ℕ | ¬IsZero (correspondenceRightRemainingFiniteTorModule f g h i z w v x n)}.Finite := by
  obtain ⟨d, hd⟩ := exists_correspondenceRightRemainingFiniteTorModule_degreeBound
    k f g h i z w v hw hv x
  refine (Set.finite_Iic d).subset ?_
  intro n hn
  change n ≤ d
  exact le_of_not_gt fun hlt => hn (hd n hlt)

end Stacks.Chow
