/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightCommonImageSquare
public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteResidueTransport
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap

/-!
# Maximal labels of the whole right finite algebra are actual triple-fibre points

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
abbrev correspondenceRightRemainingFiniteClosedFibre
    (x : correspondenceRightImageIncidence f g h i z w v) : Type u :=
  {q : correspondenceRightRemainingFiniteModel f g h i z w v x //
    correspondenceRightRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRightRemainingImageStalk f g h i z w v x)}

/-- The original triple fibre, retaining the actual point and actual finite map. -/
abbrev correspondenceRightRemainingTripleFibre
    (x : correspondenceRightImageIncidence f g h i z w v) : Type u :=
  {y : correspondenceTripleIncidence f g h i z w v //
    correspondenceTripleToRightImageIncidence f g h i z w v y = x}

/-- The local-model projection identifies its closed fibre with the original exterior fibre. -/
def correspondenceRightRemainingFiniteClosedEquivExterior
    (x : correspondenceRightImageIncidence f g h i z w v) :
    correspondenceRightRemainingFiniteClosedFibre f g h i z w v x ≃
      {q : correspondenceRightIntermediateSupportProduct f g h i z w v //
        correspondenceRightIntermediateImageMap f g h i z w v q =
          correspondenceRightImageIncidenceInclusion f g h i z w v x} := by
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let F := correspondenceRightIntermediateSupportProduct f g h i z w v
  let j := correspondenceRightImageIncidenceInclusion f g h i z w v
  let m := correspondenceRightIntermediateImageMap f g h i z w v
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
  let π := correspondenceRightRemainingFiniteModelStructure f g h i z w v x
  let H : ρ ≫ m = π ≫ (T).fromSpecStalk (j x) := pullback.condition
  let e : correspondenceRightRemainingFiniteClosedFibre f g h i z w v x →
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
      (q.2.trans (Scheme.fromSpecStalk_closedPoint (x := j x)).symm)
    exact ⟨⟨r, hs⟩, Subtype.ext hr⟩

/-- The exterior-fibre comparison is literally the native localization projection. -/
theorem correspondenceRightRemainingFiniteClosedEquivExterior_val
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteClosedFibre f g h i z w v x) :
    (correspondenceRightRemainingFiniteClosedEquivExterior f g h i z w v x q).1 =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1 := rfl

/-- The remaining Cartesian square identifies the original triple and exterior fibres. -/
def correspondenceRightRemainingTripleEquivExterior
    (x : correspondenceRightImageIncidence f g h i z w v) :
    correspondenceRightRemainingTripleFibre f g h i z w v x ≃
      {q : correspondenceRightIntermediateSupportProduct f g h i z w v //
        correspondenceRightIntermediateImageMap f g h i z w v q =
          correspondenceRightImageIncidenceInclusion f g h i z w v x} := by
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let F := correspondenceRightIntermediateSupportProduct f g h i z w v
  let C := correspondenceTripleIncidence f g h i z w v
  let j := correspondenceRightImageIncidenceInclusion f g h i z w v
  let m := correspondenceRightIntermediateImageMap f g h i z w v
  let a := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v
  let k := correspondenceTripleToRightImageIncidence f g h i z w v
  let H := correspondenceTripleToRightImageIncidence_isPullback f g h i z w v
  let e : correspondenceRightRemainingTripleFibre f g h i z w v x →
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
theorem correspondenceRightRemainingTripleEquivExterior_val
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated g]
    (y : correspondenceRightRemainingTripleFibre f g h i z w v x) :
    (correspondenceRightRemainingTripleEquivExterior f g h i z w v x y).1 =
      correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y.1 := rfl

/-- Maximality of the literal model germ prime is precisely membership in the closed fibre. -/
theorem correspondenceRightRemainingFinite_germPrime_isMaximal_iff
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    ((correspondenceRightRemainingFiniteModel f g h i z w v x).toSpecΓ q).asIdeal.IsMaximal ↔
      correspondenceRightRemainingFiniteModelStructure f g h i z w v x q =
        IsLocalRing.closedPoint (correspondenceRightRemainingImageStalk f g h i z w v x) := by
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let π := correspondenceRightRemainingFiniteModelStructure f g h i z w v x
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  have := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x
  have hprime : ((E).toSpecΓ q).asIdeal.comap (algebraMap R B) = (π q).asIdeal :=
    correspondenceRightRemainingFiniteGermPrime_comap_algebraMap f g h i z w v x q
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
def correspondenceRightRemainingFiniteClosedEquivMaximal
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    correspondenceRightRemainingFiniteClosedFibre f g h i z w v x ≃
      MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x) := by
  let E := correspondenceRightRemainingFiniteModel f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  haveI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
  let e : correspondenceRightRemainingFiniteClosedFibre f g h i z w v x → MaximalSpectrum B :=
    fun q => ⟨((E).toSpecΓ q.1).asIdeal,
      (correspondenceRightRemainingFinite_germPrime_isMaximal_iff
        f g h i z w v x hw hv q.1).mpr q.2⟩
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
      (correspondenceRightRemainingFinite_germPrime_isMaximal_iff f g h i z w v x hw hv q).mp hmax
    refine ⟨⟨q, hclosed⟩, ?_⟩
    exact MaximalSpectrum.ext (congrArg PrimeSpectrum.asIdeal hq)

/-- No maximal ideal is relabelled: it is the actual section-germ preimage. -/
theorem correspondenceRightRemainingFiniteClosedEquivMaximal_asIdeal
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (q : correspondenceRightRemainingFiniteClosedFibre f g h i z w v x) :
    (correspondenceRightRemainingFiniteClosedEquivMaximal f g h i z w v x hw hv q).asIdeal =
      (IsLocalRing.maximalIdeal
        ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q.1)).comap
        ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.germ
          ⊤ q.1 trivial).hom :=
  rfl

/-- Every maximal label of the whole finite ring is exactly one actual triple-fibre point. -/
def correspondenceRightRemainingFiniteMaximalEquivTriple
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x) ≃
      correspondenceRightRemainingTripleFibre f g h i z w v x :=
  (correspondenceRightRemainingFiniteClosedEquivMaximal f g h i z w v x hw hv).symm.trans
    ((correspondenceRightRemainingFiniteClosedEquivExterior f g h i z w v x).trans
      (correspondenceRightRemainingTripleEquivExterior f g h i z w v x).symm)

/-- The final bijection preserves the literal original exterior point of the model. -/
theorem correspondenceRightRemainingFiniteMaximalEquivTriple_projection
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (p : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    correspondenceTripleIncidenceToRightSupportProduct f g h i z w v
        (correspondenceRightRemainingFiniteMaximalEquivTriple f g h i z w v x hw hv p).1 =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x
        ((correspondenceRightRemainingFiniteClosedEquivMaximal
          f g h i z w v x hw hv).symm p).1 := by
  let q := (correspondenceRightRemainingFiniteClosedEquivMaximal f g h i z w v x hw hv).symm p
  have he := congrArg Subtype.val ((correspondenceRightRemainingTripleEquivExterior
    f g h i z w v x).apply_symm_apply
      (correspondenceRightRemainingFiniteClosedEquivExterior f g h i z w v x q))
  change correspondenceTripleIncidenceToRightSupportProduct f g h i z w v
      ((correspondenceRightRemainingTripleEquivExterior f g h i z w v x).symm
        (correspondenceRightRemainingFiniteClosedEquivExterior f g h i z w v x q)).1 =
    correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1
  simpa only [correspondenceRightRemainingTripleEquivExterior_val,
    correspondenceRightRemainingFiniteClosedEquivExterior_val] using he

/-- The maximal label remains the literal germ prime at its actual model point. -/
theorem correspondenceRightRemainingFiniteMaximalEquivTriple_germPrime
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (p : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    p.asIdeal =
      (IsLocalRing.maximalIdeal
        ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk
          ((correspondenceRightRemainingFiniteClosedEquivMaximal
            f g h i z w v x hw hv).symm p).1)).comap
        ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤
          ((correspondenceRightRemainingFiniteClosedEquivMaximal f g h i z w v x hw hv).symm p).1
          trivial).hom := by
  exact (congrArg MaximalSpectrum.asIdeal
    ((correspondenceRightRemainingFiniteClosedEquivMaximal f g h i z w v x hw hv).apply_symm_apply
      p)).symm

/-- Closing the remaining incidence does not alter the actual finite-map residue degree. -/
theorem residueDegree_correspondenceTripleToRightImageIncidence
    (y : correspondenceTripleIncidence f g h i z w v) :
    (correspondenceTripleToRightImageIncidence f g h i z w v).residueDegree y =
      (correspondenceRightIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y) := by
  let j := correspondenceRightImageIncidenceInclusion f g h i z w v
  let m := correspondenceRightIntermediateImageMap f g h i z w v
  let a := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v
  let k := correspondenceTripleToRightImageIncidence f g h i z w v
  have := isIso_residueFieldMap_of_isPreimmersion j (k y)
  have := isIso_residueFieldMap_of_isPreimmersion a y
  calc
    (k).residueDegree y = (k ≫ j).residueDegree y :=
      (residueDegree_comp_of_bijective_residueFieldMap k j y
        (ConcreteCategory.bijective_of_isIso _)).symm
    _ = (a ≫ m).residueDegree y := by
      rw [correspondenceTripleToRightImageIncidence_inclusion]
    _ = (m).residueDegree (a y) :=
      residueDegree_of_bijective_residueFieldMap_comp a m y
        (ConcreteCategory.bijective_of_isIso _)

/-- The original prime residue degree is the actual triple-to-image degree at its fibre label. -/
theorem primeResidueDegree_correspondenceRightRemainingFiniteMaximalEquivTriple
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (p : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    Stacks.Length.primeResidueDegree
      (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x))
      (p.asIdeal.comap (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x))) p.asIdeal =
      (correspondenceTripleToRightImageIncidence f g h i z w v).residueDegree
        (correspondenceRightRemainingFiniteMaximalEquivTriple f g h i z w v x hw hv p).1 := by
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let q := (correspondenceRightRemainingFiniteClosedEquivMaximal f g h i z w v x hw hv).symm p
  have hdegree :=
    primeResidueDegree_correspondenceRightRemainingFiniteAlgebra f g h i z w v hw hv x q.1
  have hprime :=
    correspondenceRightRemainingFiniteMaximalEquivTriple_germPrime f g h i z w v x hw hv p
  rw [residueDegree_correspondenceTripleToRightImageIncidence,
    correspondenceRightRemainingFiniteMaximalEquivTriple_projection]
  dsimp only [q] at hdegree
  simpa only [← hprime] using hdegree

end Stacks.Chow
