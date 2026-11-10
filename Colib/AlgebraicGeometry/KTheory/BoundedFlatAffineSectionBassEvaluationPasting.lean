/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompSplitRelative
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineBassSquare
public import Colib.Topology.Prespectrum.RelativeHomotopySquarePasting

/-!
# The original Laurent-chart evaluation pasting

The two actual Laurent inclusions specialize the proved evaluation composition coherence.
All original coefficient homotopies and geometric composition tracks are retained.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationPasting.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original positive source leg, Laurent
unit and independent whole-homotopy parameters are retained in native objects. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.RingedSpace
universe u v
private theorem outerFamilyTransport
    {X Y Z : Topology.LoopPrespectrum.{u}} {I : Type v}
    (ε : X ⟶ Y) (a : I → (X ⟶ Z)) (p : I → (Y ⟶ Z))
    (H : ∀ i, Homotopy (a i) (ε ≫ p i))
    {q r : I} (h : q = r) {w z : Y ⟶ Z} (K : Homotopy w z)
    (hw : w = p q) (t : X ⟶ Z) (ht : ε ≫ z = t)
    (β : Homotopy (a q) t)
    (hβ : β = ((H q).trans (Homotopy.precomp ε (K.cast hw rfl))).cast rfl ht) :
    (H r).trans
        ((Homotopy.precomp ε (K.cast (hw.trans (congrArg p h)) rfl)).cast rfl ht) =
      β.cast (congrArg a h) rfl := by
  subst β
  cases h
  apply Topology.LoopPrespectrum.Homotopy.ext
  funext n
  rfl

private theorem firstWholeTransport
    {X Y : Topology.LoopPrespectrum.{u}} {f f' f'' g t : X ⟶ Y}
    (H : Homotopy f g) (K : Homotopy g t) (p : f = f') (q : f' = f'')
    (α : Homotopy f'' g) (hα : α = H.cast (p.trans q) rfl)
    (β : Homotopy f' t) (hβ : β = (H.trans K).cast p rfl) :
    α.trans K = β.cast q rfl := by
  subst α
  subst β
  apply Topology.LoopPrespectrum.Homotopy.ext
  funext n
  rfl

namespace AlgebraicGeometry.Scheme.Modules

/-- A Laurent chart uses its original split geometric composition homotopy. -/
def boundedAboveFlatAffineSectionChartGeometricTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (laurentProjection R))
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map k)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (Spec.map k) (polynomialProjection
    R)).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap
      ((Spec.map_comp ((CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) k).symm.trans
        (congrArg Spec.map h))) rfl

/-- Original evaluation followed by the actual chart composition track. -/
def boundedAboveFlatAffineSectionChartOuterTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) :
    Homotopy
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      ((boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map k)) :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy (laurentCoefficientInclusion R)).trans
    ((Homotopy.precomp (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatAffineSectionChartGeometricTrack R k h)).cast rfl
        (Category.assoc _ _ _).symm)

/-- The same original chart route formed by the two coefficient evaluation tracks. -/
def boundedAboveFlatAffineSectionChartWhiskeredTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) :
    Homotopy
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      ((boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map k)) :=
  (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy ((CommRingCat.ofHom (Polynomial.C : R
    →+* Polynomial R))) k).cast
    (congrArg (fun f => boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R))) h) rfl

/-- Source endpoint transport retains the complete original whiskered track. -/
theorem boundedAboveFlatAffineSectionChartWhiskeredTrack_level (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) (n : ℕ) :
    (boundedAboveFlatAffineSectionChartWhiskeredTrack R k h).level n =
      (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy
        (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k).level n := rfl

/-- Whole equality, retaining literal original K and the forward chart equation. -/
theorem boundedAboveFlatAffineSectionChartOuterTrack_whole
    (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) :
    boundedAboveFlatAffineSectionChartOuterTrack R k h =
      (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy
        (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k).cast
        (congrArg (fun f => boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
          boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R))) h)
        rfl := by
  exact outerFamilyTransport
    (boundedAboveFlatAffineEvaluationPrespectrumMap R)
    (fun f : R ⟶ CommRingCat.of (LaurentPolynomial R) =>
      boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
    (fun f : R ⟶ CommRingCat.of (LaurentPolynomial R) =>
      boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map f))
    (fun f => boundedAboveFlatAffineEvaluationCoefficientHomotopy f)
    h
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
      (Spec.map k) (polynomialProjection R))
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap
      (Spec.map_comp (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k).symm)
    ((boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
      boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map k))
    (Category.assoc _ _ _).symm
    (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k)
    (by rfl)

/-- Project only after the whole equality; every n, including zero, is retained. -/
theorem boundedAboveFlatAffineSectionChartOuterTrack_level
    (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) (n : ℕ) :
    (boundedAboveFlatAffineSectionChartOuterTrack R k h).level n =
      (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy
        (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k).level n := by
  exact (congrArg (fun H => H.level n)
    (boundedAboveFlatAffineSectionChartOuterTrack_whole R k h)).trans
      (Homotopy.cast_level _ _ _ n)


/-- The actual chart coefficient equation identifies the full outer Laurent track. -/
def boundedAboveFlatAffineSectionChartEvaluationPasting (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) :
    (boundedAboveFlatAffineSectionChartWhiskeredTrack R k h).RelHomotopy
      (boundedAboveFlatAffineSectionChartOuterTrack R k h) := by
  let J : (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k).RelHomotopy
      (boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy
        (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k) :=
    (boundedAboveFlatAffineEvaluationCompSplitRelHomotopy
      (R := R) (S := .of (Polynomial R)) (T := .of (LaurentPolynomial R))
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k).symm
  exact Homotopy.RelHomotopy.ofLevels
    (E := boundedAboveFlatAffineSectionPrespectrumFunctor.obj R)
    (F := originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (Spec (.of (LaurentPolynomial R))).toRingedSpace))
    (H := boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k)
    (K := boundedAboveFlatAffineEvaluationCompSplitLeftHomotopy
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k)
    J (boundedAboveFlatAffineSectionChartWhiskeredTrack R k h)
    (boundedAboveFlatAffineSectionChartOuterTrack R k h)
    (boundedAboveFlatAffineSectionChartWhiskeredTrack_level R k h)
    (boundedAboveFlatAffineSectionChartOuterTrack_level R k h)

/-- The first whiskered coefficient track, transported by the actual strict chart equation. -/
def boundedAboveFlatAffineSectionChartFirstTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) :
    Homotopy
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
      ((boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R))) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map k)) :=
  (Homotopy.precomp (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom
    (Polynomial.C : R →+* Polynomial R))))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy k)).cast
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map_comp ((CommRingCat.ofHom
          (Polynomial.C : R →+* Polynomial R))) k).symm.trans
          (congrArg boundedAboveFlatAffineSectionPrespectrumFunctor.map h))))
    (Category.assoc _ _ _).symm

/-- Strict chart endpoint transport changes no value of the original precomposed track. -/
theorem boundedAboveFlatAffineSectionChartFirstTrack_level (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) (n : ℕ) :
    (boundedAboveFlatAffineSectionChartFirstTrack R k h).level n =
      (Homotopy.precomp (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom
        (Polynomial.C : R →+* Polynomial R))))
        (boundedAboveFlatAffineEvaluationCoefficientHomotopy k)).level n := rfl

/-- The original chart evaluation track on the literal uncollapsed strict source leg. -/
def boundedAboveFlatAffineSectionChartMovingTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R)) :=
  (Homotopy.precomp (boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom
    (Polynomial.C : R →+* Polynomial R))))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy k)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- Collapsing only the strict chart equation retains every original moving-track value. -/
theorem boundedAboveFlatAffineSectionChartMovingTrack_level (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) (n : ℕ) :
    (boundedAboveFlatAffineSectionChartMovingTrack R k).level n =
      (boundedAboveFlatAffineSectionChartFirstTrack R k h).level n := by
  exact (Homotopy.cast_level _ _ _ n).trans
    (boundedAboveFlatAffineSectionChartFirstTrack_level R k h n).symm

/-- The second coefficient track retains original geometric postcomposition. -/
def boundedAboveFlatAffineSectionChartSecondTrack (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R)) :
    Homotopy
      ((boundedAboveFlatAffineSectionPrespectrumFunctor.map ((CommRingCat.ofHom (Polynomial.C : R
        →+* Polynomial R))) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (Polynomial R))) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map k))
      ((boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap (polynomialProjection R)) ≫
          boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map k)) :=
  (boundedAboveFlatAffineEvaluationCoefficientHomotopy ((CommRingCat.ofHom (Polynomial.C : R →+*
    Polynomial R)))).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (Spec.map k))

/-- Whole first/second route, with no assumed comparison filler. -/
theorem boundedAboveFlatAffineSectionChartFirstWhiskered_whole
    (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) :
    (boundedAboveFlatAffineSectionChartFirstTrack R k h).trans
        (boundedAboveFlatAffineSectionChartSecondTrack R k) =
      boundedAboveFlatAffineSectionChartWhiskeredTrack R k h := by
  exact firstWholeTransport
    ((Homotopy.precomp (boundedAboveFlatAffineSectionPrespectrumFunctor.map
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy k)).cast rfl
        (Category.assoc _ _ _).symm)
    (boundedAboveFlatAffineSectionChartSecondTrack R k)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun a => a ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R)))
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map_comp
          (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k).symm))
    (congrArg (fun f => boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
      boundedAboveFlatAffineEvaluationPrespectrumMap (.of (LaurentPolynomial R))) h)
    (boundedAboveFlatAffineSectionChartFirstTrack R k h) (by rfl)
    (boundedAboveFlatAffineEvaluationCompIteratedLeftHomotopy
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) k) (by rfl)

/-- Project only the established whole equality, for arbitrary level n. -/
theorem boundedAboveFlatAffineSectionChartFirstTrack_trans_level
    (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) (n : ℕ) :
    ((boundedAboveFlatAffineSectionChartFirstTrack R k h).trans
      (boundedAboveFlatAffineSectionChartSecondTrack R k)).level n =
      (boundedAboveFlatAffineSectionChartWhiskeredTrack R k h).level n :=
  congrArg (fun H => H.level n)
    (boundedAboveFlatAffineSectionChartFirstWhiskered_whole R k h)


/-- The actual two coefficient tracks form the proved chart evaluation pasting. -/
def boundedAboveFlatAffineSectionChartFirstPasting (R : CommRingCat.{u})
    (k : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of (LaurentPolynomial R))
    (h : (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫ k =
      laurentCoefficientInclusion R) :
    ((boundedAboveFlatAffineSectionChartFirstTrack R k h).trans
      (boundedAboveFlatAffineSectionChartSecondTrack R k)).RelHomotopy
        (boundedAboveFlatAffineSectionChartOuterTrack R k h) :=
  Homotopy.RelHomotopy.ofLevels
    (E := boundedAboveFlatAffineSectionPrespectrumFunctor.obj R)
    (F := originalPrespectrum (boundedAboveFlatPerfectWaldhausen
      (Spec (.of (LaurentPolynomial R))).toRingedSpace))
    (H := boundedAboveFlatAffineSectionChartWhiskeredTrack R k h)
    (K := boundedAboveFlatAffineSectionChartOuterTrack R k h)
    (boundedAboveFlatAffineSectionChartEvaluationPasting R k h)
    ((boundedAboveFlatAffineSectionChartFirstTrack R k h).trans
      (boundedAboveFlatAffineSectionChartSecondTrack R k))
    (boundedAboveFlatAffineSectionChartOuterTrack R k h)
    (boundedAboveFlatAffineSectionChartFirstTrack_trans_level R k h) (fun _ => rfl)

/-- The genuine positive Laurent chart supplies its exact evaluation pasting. -/
def boundedAboveFlatAffineSectionPlusEvaluationPasting (R : CommRingCat.{u}) :=
  boundedAboveFlatAffineSectionChartEvaluationPasting R (CommRingCat.ofHom Polynomial.toLaurent)
    (coefficient_toLaurent R)

/-- The separate inverse-coordinate Laurent chart supplies its exact evaluation pasting. -/
def boundedAboveFlatAffineSectionMinusEvaluationPasting (R : CommRingCat.{u}) :=
  boundedAboveFlatAffineSectionChartEvaluationPasting R
    (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
    (coefficient_toLaurent_invert R)

/-- The positive geometric chart track is exactly the previously constructed original track. -/
theorem boundedAboveFlatAffineSectionChartGeometricTrack_plus (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionChartGeometricTrack R (CommRingCat.ofHom Polynomial.toLaurent)
      (coefficient_toLaurent R) =
        boundedAboveFlatLaurentPlusHomotopy R := rfl

/-- The negative geometric track retains the original inverse-coordinate leg and its timing. -/
theorem boundedAboveFlatAffineSectionChartGeometricTrack_minus (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionChartGeometricTrack R
      (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent))
      (coefficient_toLaurent_invert R) =
        boundedAboveFlatLaurentMinusHomotopy R := rfl

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassEvaluationPasting.lean:32-175"
  "adaptation" "Actual split-to-whiskered coefficient comparison specialized to each Laurent chart"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionChartFirstPasting
