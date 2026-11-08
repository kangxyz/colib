/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteGenericLabels
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteResidueTransport
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap

/-!
# Maximal labels of the whole finite algebra are actual triple-fibre points

The ring is the existing global-section ring of the full local base change. Its maximal
ideals are identified with the closed fibre of that same affine model, using the native
Gamma-Spec equivalence and integrality over the actual image local ring. The localization
projection then identifies this fibre with the original full exterior fibre. Finally the
proved remaining-incidence Cartesian square identifies that fibre with the original triple
incidence over the given image-incidence point.

The intermediate point, its literal section-germ prime, the original exterior projection,
and the residue degree are retained. No generic-point identification, reduction, choice of
one component, or replacement of the full finite algebra by a source stalk is made.

## References

* Mathlib `GammaSpecAdjunction` and `AffineScheme`: the actual affine Gamma-Spec equivalence.
* Mathlib `Ideal/GoingUp`: maximal ideals above a maximal ideal under an integral map.
* Stacks Project, Tag 01J7: the local-scheme projection, used by `RemainingFiniteModel`.
* Stacks Project, Tag 02R4: the residue degree retained in finite cycle pushforward.

This file specializes native constructions; it does not introduce another finite model.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual model's closed fibre, with an explicit original image-point parameter. -/
abbrev correspondenceRemainingFiniteClosedFibre
    (x : correspondenceLeftImageIncidence f g h i z w v) : Type u :=
  {q : correspondenceRemainingFiniteModel f g h i z w v x //
    correspondenceRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x)}

/-- The original triple fibre, retaining the actual point and actual finite map. -/
abbrev correspondenceRemainingTripleFibre
    (x : correspondenceLeftImageIncidence f g h i z w v) : Type u :=
  {y : correspondenceTripleIncidence f g h i z w v //
    correspondenceTripleToLeftImageIncidence f g h i z w v y = x}

/-- The local-model projection identifies its closed fibre with the original exterior fibre. -/
def correspondenceRemainingFiniteClosedEquivExterior
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    correspondenceRemainingFiniteClosedFibre f g h i z w v x ≃
      {q : correspondenceLeftIntermediateSupportProduct f g h i z w v //
        correspondenceLeftIntermediateImageMap f g h i z w v q =
          correspondenceLeftImageIncidenceInclusion f g h i z w v x} := by
  let T := correspondenceLeftIntermediateImageProduct f g h i z w v
  let F := correspondenceLeftIntermediateSupportProduct f g h i z w v
  let j := correspondenceLeftImageIncidenceInclusion f g h i z w v
  let m := correspondenceLeftIntermediateImageMap f g h i z w v
  let E := correspondenceRemainingFiniteModel f g h i z w v x
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  let H : ρ ≫ m = π ≫ (T).fromSpecStalk (j x) := pullback.condition
  let e : correspondenceRemainingFiniteClosedFibre f g h i z w v x →
      {q : F // m q = j x} := fun q => ⟨ρ q.1, by
    have hpoint := congrArg (fun u : E ⟶ T => u q.1) H
    change m (ρ q.1) = (T).fromSpecStalk (j x) (π q.1) at hpoint
    rw [hpoint, q.2, Scheme.fromSpecStalk_closedPoint]⟩
  apply Equiv.ofBijective e
  constructor
  · intro q q' hq
    apply Subtype.ext
    exact (ρ).isEmbedding.injective (congrArg Subtype.val hq)
  · intro q
    obtain ⟨r, hr, hs⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := m) (g := (T).fromSpecStalk (j x)) q.1 (IsLocalRing.closedPoint R)
      (by simpa only [Scheme.fromSpecStalk_closedPoint] using q.2)
    exact ⟨⟨r, hs⟩, Subtype.ext hr⟩

/-- The exterior-fibre comparison is literally the native localization projection. -/
theorem correspondenceRemainingFiniteClosedEquivExterior_val
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteClosedFibre f g h i z w v x) :
    (correspondenceRemainingFiniteClosedEquivExterior f g h i z w v x q).1 =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q.1 := rfl

/-- The remaining Cartesian square identifies the original triple and exterior fibres. -/
def correspondenceRemainingTripleEquivExterior
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h] :
    correspondenceRemainingTripleFibre f g h i z w v x ≃
      {q : correspondenceLeftIntermediateSupportProduct f g h i z w v //
        correspondenceLeftIntermediateImageMap f g h i z w v q =
          correspondenceLeftImageIncidenceInclusion f g h i z w v x} := by
  let T := correspondenceLeftIntermediateImageProduct f g h i z w v
  let F := correspondenceLeftIntermediateSupportProduct f g h i z w v
  let C := correspondenceTripleIncidence f g h i z w v
  let j := correspondenceLeftImageIncidenceInclusion f g h i z w v
  let m := correspondenceLeftIntermediateImageMap f g h i z w v
  let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v
  let k := correspondenceTripleToLeftImageIncidence f g h i z w v
  let H := correspondenceTripleToLeftImageIncidence_isPullback f g h i z w v
  let e : correspondenceRemainingTripleFibre f g h i z w v x →
      {q : F // m q = j x} := fun y => ⟨a y.1, by
    have hpoint := congrArg (fun u : C ⟶ T => u y.1) H.w
    change j (k y.1) = m (a y.1) at hpoint
    rw [← hpoint, y.2]⟩
  apply Equiv.ofBijective e
  constructor
  · intro y y' hy
    apply Subtype.ext
    exact (a).isEmbedding.injective (congrArg Subtype.val hy)
  · intro q
    obtain ⟨y, hy, hq⟩ := Scheme.exists_preimage_of_isPullback H x q.1 q.2.symm
    exact ⟨⟨y, hy⟩, Subtype.ext hq⟩

/-- The triple-fibre comparison keeps the original full exterior support point. -/
theorem correspondenceRemainingTripleEquivExterior_val
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h]
    (y : correspondenceRemainingTripleFibre f g h i z w v x) :
    (correspondenceRemainingTripleEquivExterior f g h i z w v x y).1 =
      correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y.1 := rfl

/-- Maximality of the literal model germ prime is precisely membership in the closed fibre. -/
theorem correspondenceRemainingFinite_germPrime_isMaximal_iff
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    ((correspondenceRemainingFiniteModel f g h i z w v x).toSpecΓ q).asIdeal.IsMaximal ↔
      correspondenceRemainingFiniteModelStructure f g h i z w v x q =
        IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x) := by
  let E := correspondenceRemainingFiniteModel f g h i z w v x
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let B := correspondenceRemainingFiniteRing f g h i z w v x
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  have := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x
  have hprime : ((E).toSpecΓ q).asIdeal.comap (algebraMap R B) = (π q).asIdeal :=
    correspondenceRemainingFiniteGermPrime_comap_algebraMap f g h i z w v x q
  constructor
  · intro hq
    have := hq
    have hu := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
      ((E).toSpecΓ q).asIdeal
    change (((E).toSpecΓ q).asIdeal.comap (algebraMap R B)).IsMaximal at hu
    rw [hprime] at hu
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hu)
  · intro hq
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R)
    change (((E).toSpecΓ q).asIdeal.comap (algebraMap R B)).IsMaximal
    rw [hprime, hq]
    exact IsLocalRing.maximalIdeal.isMaximal R

/-- The native affine Gamma-Spec map identifies the whole closed fibre with all maximal ideals. -/
def correspondenceRemainingFiniteClosedEquivMaximal
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    correspondenceRemainingFiniteClosedFibre f g h i z w v x ≃
      MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) := by
  let E := correspondenceRemainingFiniteModel f g h i z w v x
  let B := correspondenceRemainingFiniteRing f g h i z w v x
  haveI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  let e : correspondenceRemainingFiniteClosedFibre f g h i z w v x → MaximalSpectrum B :=
    fun q => ⟨((E).toSpecΓ q.1).asIdeal,
      (correspondenceRemainingFinite_germPrime_isMaximal_iff f g h i z w v x hz hw q.1).mpr q.2⟩
  apply Equiv.ofBijective e
  constructor
  · intro q q' hq
    apply Subtype.ext
    apply (Scheme.homeoOfIso (asIso (E).toSpecΓ)).injective
    exact PrimeSpectrum.ext (congrArg MaximalSpectrum.asIdeal hq)
  · intro p
    obtain ⟨q, hq⟩ := (Scheme.homeoOfIso (asIso (E).toSpecΓ)).surjective p.toPrimeSpectrum
    have hmax : ((E).toSpecΓ q).asIdeal.IsMaximal := by
      rw [show (E).toSpecΓ q = p.toPrimeSpectrum from hq]
      exact p.isMaximal
    have hclosed :=
      (correspondenceRemainingFinite_germPrime_isMaximal_iff f g h i z w v x hz hw q).mp hmax
    refine ⟨⟨q, hclosed⟩, ?_⟩
    exact MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal hq)

/-- No maximal ideal is relabelled: it is the actual section-germ preimage. -/
theorem correspondenceRemainingFiniteClosedEquivMaximal_asIdeal
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (q : correspondenceRemainingFiniteClosedFibre f g h i z w v x) :
    (correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw q).asIdeal =
      (IsLocalRing.maximalIdeal
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q.1)).comap
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q.1 trivial).hom :=
  rfl

/-- Every maximal label of the whole finite ring is exactly one actual triple-fibre point. -/
def correspondenceRemainingFiniteMaximalEquivTriple
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) ≃
      correspondenceRemainingTripleFibre f g h i z w v x :=
  (correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw).symm.trans
    ((correspondenceRemainingFiniteClosedEquivExterior f g h i z w v x).trans
      (correspondenceRemainingTripleEquivExterior f g h i z w v x).symm)

/-- The final bijection preserves the literal original exterior point of the model. -/
theorem correspondenceRemainingFiniteMaximalEquivTriple_projection
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v
        (correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw p).1 =
      correspondenceRemainingFiniteModelProjection f g h i z w v x
        ((correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw).symm p).1 := by
  let q := (correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw).symm p
  exact congrArg Subtype.val ((correspondenceRemainingTripleEquivExterior
    f g h i z w v x).apply_symm_apply
      (correspondenceRemainingFiniteClosedEquivExterior f g h i z w v x q))

/-- The maximal label remains the literal germ prime at its actual model point. -/
theorem correspondenceRemainingFiniteMaximalEquivTriple_germPrime
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    p.asIdeal =
      (IsLocalRing.maximalIdeal ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk
        ((correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw).symm p).1)).comap
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤
          ((correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw).symm p).1
          trivial).hom := by
  exact (congrArg MaximalSpectrum.asIdeal
    ((correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw)
      .apply_symm_apply p)).symm

/-- Closing the remaining incidence does not alter the actual finite-map residue degree. -/
theorem residueDegree_correspondenceTripleToLeftImageIncidence [IsSeparated h]
    (y : correspondenceTripleIncidence f g h i z w v) :
    (correspondenceTripleToLeftImageIncidence f g h i z w v).residueDegree y =
      (correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y) := by
  let j := correspondenceLeftImageIncidenceInclusion f g h i z w v
  let m := correspondenceLeftIntermediateImageMap f g h i z w v
  let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v
  let k := correspondenceTripleToLeftImageIncidence f g h i z w v
  have := isIso_residueFieldMap_of_isPreimmersion j (k y)
  have := isIso_residueFieldMap_of_isPreimmersion a y
  calc
    (k).residueDegree y = (k ≫ j).residueDegree y :=
      (residueDegree_comp_of_bijective_residueFieldMap k j y
        (ConcreteCategory.bijective_of_isIso _)).symm
    _ = (a ≫ m).residueDegree y := by
      rw [correspondenceTripleToLeftImageIncidence_inclusion]
    _ = (m).residueDegree (a y) :=
      residueDegree_of_bijective_residueFieldMap_comp a m y
        (ConcreteCategory.bijective_of_isIso _)

/-- The original prime residue degree is the actual triple-to-image degree at its fibre label. -/
theorem primeResidueDegree_correspondenceRemainingFiniteMaximalEquivTriple
    (x : correspondenceLeftImageIncidence f g h i z w v) [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x))
      (p.asIdeal.comap (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x))) p.asIdeal =
      (correspondenceTripleToLeftImageIncidence f g h i z w v).residueDegree
        (correspondenceRemainingFiniteMaximalEquivTriple f g h i z w v x hz hw p).1 := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let q := (correspondenceRemainingFiniteClosedEquivMaximal f g h i z w v x hz hw).symm p
  rw [correspondenceRemainingFiniteMaximalEquivTriple_germPrime f g h i z w v x hz hw p,
    primeResidueDegree_correspondenceRemainingFiniteAlgebra f g h i z w v hz hw x q.1,
    residueDegree_correspondenceTripleToLeftImageIncidence,
    correspondenceRemainingFiniteMaximalEquivTriple_projection]

end Stacks.Chow
