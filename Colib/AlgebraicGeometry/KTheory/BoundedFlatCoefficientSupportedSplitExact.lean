/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedUnitQuotient
public import Colib.KTheory.Bass.TwoChartSplitExact
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedMiddleTransport
public import Colib.KTheory.Bass.ModelDiagramTwoChartStableSequence

/-!
# Two naturally split rows for the original supported coefficient spectrum

Actual polynomial zero evaluation splits the original common corner. The genuine inverse
Laurent Model action and its original quotient isomorphism define the canonical boundary and
split the second row. Consequently every additive endofunctor of coefficient group diagrams
preserves the original positive middle row. The ambient scheme is qcqs and the removed open
is compact. The canonical boundary is not identified here with a geometric projective-line
first-coordinate boundary or a transported perfect scalar operation.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedSplitExact.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Topology Topology.LoopPrespectrum KTheory.Bass KTheory.Bass.TwoChart
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Evaluation at zero is natural on the original category of coefficient algebras. -/
def modelDiagramPolynomialZeroNat (R : CommRingCat.{u}) : polynomialUnderFunctor R ⟶ 𝟭 _ where
  app := modelDiagramPolynomialZero
  naturality {a b} g := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    ext p
    change (Polynomial.map g.right.hom p).eval 0 = g.right.hom (p.eval 0)
    simpa only [map_zero] using Polynomial.eval_map_apply (p := p) g.right.hom 0

/-- Zero evaluation retracts the same original polynomial coefficient inclusion. -/
lemma modelDiagramPolynomialZeroNat_retraction (R : CommRingCat.{u}) :
    polynomialUnderCoefficient R ≫ modelDiagramPolynomialZeroNat R = 𝟙 _ := by
  apply NatTrans.ext
  funext a
  exact modelDiagramPolynomialCoefficient_zero a

/-- The unchanged stable groups of the original supported section Model. -/
def boundedAboveFlatCoefficientSupportedStableGroupFunctor (d : ℤ) :
    Under R ⥤ AddCommGrpCat.{u + 1} :=
  boundedAboveFlatCoefficientSupportedPrespectrumFunctor f ⋙ stableHomotopyFunctor d

/-- The original supported corner and signed Laurent chart difference. -/
def boundedAboveFlatCoefficientSupportedMiddleSequence (d : ℤ) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{u + 1}) :=
  middleComplex (polynomialUnderCoefficient R) (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientSupportedCommonCorner (R := R))
    (boundedAboveFlatCoefficientSupportedStableGroupFunctor f d)

/-- Actual zero evaluation naturally splits the original supported corner quotient row. -/
def boundedAboveFlatCoefficientSupportedCornerSplitting (d : ℤ) :
    (ShortComplex.cokernelSequence
      (boundedAboveFlatCoefficientSupportedMiddleSequence f d).f).Splitting :=
  middleCornerSplitting (polynomialUnderCoefficient R) (underToLaurent R)
    (underToLaurentInvert R) ((modelDiagramPolynomialZeroNat R))
      ((modelDiagramPolynomialZeroNat_retraction R))
      (boundedAboveFlatCoefficientSupportedStableGroupFunctor f d)

/-- The actual inverse supported Laurent unit as a natural degree-raising section. -/
def boundedAboveFlatCoefficientSupportedInverseUnitSection (d : ℤ) :
    boundedAboveFlatCoefficientSupportedStableGroupFunctor f d ⟶
      laurentUnderFunctor R ⋙ boundedAboveFlatCoefficientSupportedStableGroupFunctor f (d + 1) :=
  (boundedAboveFlatCoefficientSupportedInverseLaurentAction f).track.stableOperationNatTrans d

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The actual supported middle row is exact in each nonnegative stable degree. -/
theorem boundedAboveFlatCoefficientSupportedMiddleSequence_exact (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedMiddleSequence f (n : ℤ)).Exact := by
  apply middleComplex_exact_of_pointwise
  intro a
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (boundedAboveFlatCoefficientSupportedStageZeroChart_exact f a n)

/-- The specified inverse section followed by the original quotient is the proved isomorphism.
-/
instance boundedAboveFlatCoefficientSupportedInverseSectionQuotient_isIso (n : ℕ) :
    IsIso (boundedAboveFlatCoefficientSupportedInverseUnitSection f (n : ℤ) ≫
      contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))) :=
  boundedAboveFlatCoefficientSupportedInverseUnitQuotient_isIso f n

/-- The natural boundary determined by the original inverse unit and the original quotient. -/
def boundedAboveFlatCoefficientSupportedCanonicalBoundary (n : ℕ) :
    (laurentUnderFunctor R ⋙
      boundedAboveFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1)) ⟶
      boundedAboveFlatCoefficientSupportedStableGroupFunctor f (n : ℤ) :=
  unitQuotientBoundary (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))
    (boundedAboveFlatCoefficientSupportedStableGroupFunctor f (n : ℤ))
    (boundedAboveFlatCoefficientSupportedInverseUnitSection f (n : ℤ))

/-- The specified original inverse unit splits this same canonical quotient boundary. -/
@[reassoc (attr := simp)]
theorem boundedAboveFlatCoefficientSupportedInverseUnitSection_boundary (n : ℕ) :
    boundedAboveFlatCoefficientSupportedInverseUnitSection f (n : ℤ) ≫
      boundedAboveFlatCoefficientSupportedCanonicalBoundary f n = 𝟙 _ :=
  section_unitQuotientBoundary (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))
    (boundedAboveFlatCoefficientSupportedStableGroupFunctor f (n : ℤ))
    (boundedAboveFlatCoefficientSupportedInverseUnitSection f (n : ℤ))

/-- The original corner quotient, Laurent group and coefficient group form a genuinely split
natural boundary row. -/
def boundedAboveFlatCoefficientSupportedBoundarySplitting (n : ℕ) :
    (splitUnitQuotientBoundarySequence (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedAboveFlatCoefficientSupportedCommonCorner (R := R))
      (boundedAboveFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))
      (boundedAboveFlatCoefficientSupportedStableGroupFunctor f (n : ℤ))
      (boundedAboveFlatCoefficientSupportedInverseUnitSection f (n : ℤ))).Splitting := by
  apply unitQuotientBoundarySplitting
  exact boundedAboveFlatCoefficientSupportedMiddleSequence_exact f (n + 1)

/-- Every additive endofunctor preserves this original positive supported middle row by its two
constructed splittings. -/
theorem boundedAboveFlatCoefficientSupportedMiddleSequence_map_exact (n : ℕ)
    (T : (Under R ⥤ AddCommGrpCat.{u + 1}) ⥤ (Under R ⥤ AddCommGrpCat.{u + 1}))
    [T.Additive] :
    ((boundedAboveFlatCoefficientSupportedMiddleSequence f ((n : ℤ) + 1)).map T).Exact :=
  middleComplex_map_exact (polynomialUnderCoefficient R) (underToLaurent R)
    (underToLaurentInvert R) (boundedAboveFlatCoefficientSupportedCommonCorner (R := R))
    (boundedAboveFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))
    (boundedAboveFlatCoefficientSupportedStableGroupFunctor f (n : ℤ))
    (boundedAboveFlatCoefficientSupportedInverseUnitSection f (n : ℤ))
    ((modelDiagramPolynomialZeroNat R)) ((modelDiagramPolynomialZeroNat_retraction R))
    (boundedAboveFlatCoefficientSupportedMiddleSequence_exact f (n + 1)) T

end AlgebraicGeometry.Scheme.Modules
