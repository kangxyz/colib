/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentBaseChange
public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.KTheory.Bass.ModelDiagramConnectivity
public import Colib.KTheory.Bass.TwoChartStableSequence
public import Colib.Topology.Prespectrum.PushoutLinearExcision
public import Colib.Topology.Prespectrum.PositiveLevelEquivalence

/-!
Source: `Quillen/KTheory/Bass/ModelDiagramTwoChartStableSequence.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original spectral Bass row at every finite coefficient Model stage

Literal polynomial evaluation at zero is an arrow in `Under R` retracting the original
coefficient inclusion. Applying the actual finite Bass functor therefore gives a strict
prespectrum retraction, without identifying any chosen geometric pullbacks. The original
finite Model point HEP and all-point growth prove all three original cone-to-fiber excisions;
the original right-cone collapse is stable by its proved levelwise collapse theorem.

Thus all inputs of the structural spectral row are constructed from the actual Model diagram.
No chart middle exactness, fundamental sequence, or original seed preservation is an input.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory CategoryTheory.Limits Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
universe u w
namespace KTheory.Bass

variable {R : CommRingCat.{u}}

/-- The original polynomial evaluation at zero, retaining the fixed coefficient algebra map. -/
def modelDiagramPolynomialZero (a : Under R) : (polynomialUnderFunctor R).obj a ⟶ a :=
  Under.homMk (CommRingCat.ofHom (Polynomial.evalRingHom (0 : a.right))) (by
    change (a.hom ≫ CommRingCat.ofHom (Polynomial.C : a.right →+* Polynomial a.right)) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : a.right)) = a.hom
    have hc : CommRingCat.ofHom (Polynomial.C : a.right →+* Polynomial a.right) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : a.right)) = 𝟙 a.right := by
      apply CommRingCat.hom_ext
      ext x
      change Polynomial.eval 0 (Polynomial.C x) = x
      simp
    rw [Category.assoc, hc, Category.comp_id])

/-- Actual coefficient inclusion followed by actual zero evaluation is strictly the identity. -/
@[reassoc]
theorem modelDiagramPolynomialCoefficient_zero (a : Under R) :
    (polynomialUnderCoefficient R).app a ≫ modelDiagramPolynomialZero a = 𝟙 a := by
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  ext x
  change Polynomial.eval 0 (Polynomial.C x) = x
  simp

/-- The same original finite Model Bass diagram used by the coefficient producers. -/
def modelDiagramTwoChartDiagram
    (F : Under R ⥤ WideSubcategory preservesZero.{w}) (i : ℕ) :
    Under R ⥤ LoopPrespectrum.{w} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj (F ⋙ prespectrumFunctor)

/-- The original coefficient square, mapped through the unchanged finite Model Bass diagram. -/
def modelDiagramTwoChartSquare
    (F : Under R ⥤ WideSubcategory preservesZero.{w}) (i : ℕ) (a : Under R) :
    Arrow (Arrow LoopPrespectrum.{w}) :=
  (modelDiagramTwoChartDiagram F i).mapArrow.mapArrow.obj (laurentUnderSquare R a)

variable
    (F : Under R ⥤ WideSubcategory preservesZero.{w}) (i : ℕ) (a : Under R)

/-- Actual zero evaluation at the unchanged finite stage, with no degree restriction. -/
def modelDiagramTwoChartRetraction :
    (modelDiagramTwoChartSquare F i a).left.right ⟶
      (modelDiagramTwoChartSquare F i a).left.left :=
  (modelDiagramTwoChartDiagram F i).map (modelDiagramPolynomialZero a)

/-- The original plus leg has a literal prespectrum retraction at every finite Model stage. -/
@[reassoc]
theorem modelDiagramTwoChartRetraction_eq :
    (modelDiagramTwoChartSquare F i a).left.hom ≫
      modelDiagramTwoChartRetraction F i a = 𝟙 (modelDiagramTwoChartSquare F i a).left.left := by
  change (modelDiagramTwoChartDiagram F i).map ((polynomialUnderCoefficient R).app a) ≫
    (modelDiagramTwoChartDiagram F i).map (modelDiagramPolynomialZero a) = _
  rw [← Functor.map_comp, modelDiagramPolynomialCoefficient_zero]
  exact (modelDiagramTwoChartDiagram F i).map_id a

/-- Genuine finite Model point topology and growth give excision for the original plus arrow. -/
theorem modelDiagramTwoChartPlus_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (modelDiagramTwoChartSquare F i a).left.hom) :=
  mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ i
    (fun n => modelDiagramIterate_point_homotopyExtensionProperty
      (laurentUnderSquareFunctor R) i F a (n + i + 2))
    (fun n => modelDiagramIterate_point_homotopyExtensionProperty
      (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + i + 2))
    (fun n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_at
      (laurentUnderSquareFunctor R) i F a n k hk x)
    (fun n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_at
      (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) n k hk x)

/-- Actual finite Model geometry gives excision for the unchanged pushout right inclusion. -/
theorem modelDiagramTwoChartRight_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (HomotopyPushout.inr
      (modelDiagramTwoChartSquare F i a).left.hom
      (modelDiagramTwoChartSquare F i a).hom.left)) :=
  HomotopyPushout.inr_coneFiber_isStableEquivalence_of_linearGrowth _ _ i
    (fun n => modelDiagramIterate_point_homotopyExtensionProperty
      (laurentUnderSquareFunctor R) i F a (n + i + 2))
    (fun n => modelDiagramIterate_point_homotopyExtensionProperty
      (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + i + 2))
    (fun n => modelDiagramIterate_point_homotopyExtensionProperty
      (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + i + 2))
    (fun n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_at
      (laurentUnderSquareFunctor R) i F a n k hk x)
    (fun n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_at
      (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) n k hk x)
    (fun n x k hk => modelDiagramIterate_homotopyGroup_subsingleton_at
      (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) n k hk x)

/-- The original right-cone collapse is stable by its actual levelwise point-HEP theorem. -/
theorem modelDiagramTwoChartCollapse_isStableEquivalence :
    IsStableEquivalence (HomotopyPushout.rightConeCollapse
      (modelDiagramTwoChartSquare F i a).left.hom
      (modelDiagramTwoChartSquare F i a).hom.left) :=
  isStableEquivalence_of_positiveLevel _ (fun n =>
    HomotopyPushout.rightConeCollapse_level_isWeakHomotopyEquivalence _ _ (n + 1)
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F a (n + 1))
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + 1))
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + 1)))

/-- All four actual Model corners discharge the original span-to-Laurent comparison excision. -/
theorem modelDiagramTwoChartComparison_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison
      (StrictSquare.comparison (modelDiagramTwoChartSquare F i a))) := by
  let S := modelDiagramTwoChartSquare F i a
  apply mappingConeFiberComparison_isStableEquivalence_of_linearGrowth
    (StrictSquare.comparison S) i
  · intro n
    exact HomotopyPushout.point_homotopyExtensionProperty S.left.hom S.hom.left (n + i + 2)
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F a (n + i + 2))
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + i + 2))
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + i + 2))
  · intro n
    exact modelDiagramIterate_point_homotopyExtensionProperty
      (laurentUnderSquareFunctor R) i F ((laurentUnderFunctor R).obj a) (n + i + 2)
  · intro n x k hk
    exact HomotopyPushout.homotopyGroup_subsingleton S.left.hom S.hom.left (n + i + 2) n
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F a (n + i + 2))
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + i + 2))
      (modelDiagramIterate_point_homotopyExtensionProperty
        (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) (n + i + 2))
      (fun y t ht => modelDiagramIterate_homotopyGroup_subsingleton_at
        (laurentUnderSquareFunctor R) i F a n t ht y)
      (fun y t ht => modelDiagramIterate_homotopyGroup_subsingleton_at
        (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) n t ht y)
      (fun y t ht => modelDiagramIterate_homotopyGroup_subsingleton_at
        (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) n t ht y) x k hk
  · intro n x k hk
    exact modelDiagramIterate_homotopyGroup_subsingleton_at
      (laurentUnderSquareFunctor R) i F ((laurentUnderFunctor R).obj a) n k hk x

/-- Every retained structural-row input is constructed for the actual finite coefficient Model.
-/
def modelDiagramTwoChartSpectralConditions :
    KTheory.Bass.TwoChartStable.SpectralConditions (modelDiagramTwoChartSquare F i a) where
  retraction := modelDiagramTwoChartRetraction F i a
  retraction_eq := modelDiagramTwoChartRetraction_eq F i a
  plus_excision := modelDiagramTwoChartPlus_coneFiber_isStableEquivalence F i a
  right_excision := modelDiagramTwoChartRight_coneFiber_isStableEquivalence F i a
  collapse_stable := modelDiagramTwoChartCollapse_isStableEquivalence F i a
  comparison_excision := modelDiagramTwoChartComparison_coneFiber_isStableEquivalence F i a

/-- The actual coefficient Model square has the original spectral row in every integer degree. -/
def modelDiagramTwoChartSequence (d : ℤ) : ShortComplex AddCommGrpCat :=
  KTheory.Bass.TwoChartStable.bassSequence (modelDiagramTwoChartSquare F i a)
    (modelDiagramTwoChartSpectralConditions F i a) d

/-- No additional retraction, topology, excision or chart exactness hypothesis remains. -/
theorem modelDiagramTwoChartSequence_shortExact (d : ℤ) :
    (modelDiagramTwoChartSequence F i a d).ShortExact :=
  KTheory.Bass.TwoChartStable.bassSequence_shortExact _ _ d

variable {a : Under R}

/-- Original coefficient maps act on all four corners of the actual finite Model square. -/
def modelDiagramTwoChartSquareMap {b : Under R} (g : a ⟶ b) :
    modelDiagramTwoChartSquare F i a ⟶ modelDiagramTwoChartSquare F i b :=
  (modelDiagramTwoChartDiagram F i).mapArrow.mapArrow.map (laurentUnderSquareMap R g)

/-- Original coefficient maps give morphisms of the realized all-integer spectral rows. -/
def modelDiagramTwoChartSequenceMap {b : Under R} (g : a ⟶ b) (d : ℤ) :
    modelDiagramTwoChartSequence F i a d ⟶ modelDiagramTwoChartSequence F i b d :=
  KTheory.Bass.TwoChartStable.bassSequenceMap (modelDiagramTwoChartSquareMap F i g)
    (modelDiagramTwoChartSpectralConditions F i a)
    (modelDiagramTwoChartSpectralConditions F i b) d

/-- The middle arrow is the unchanged original Bass action on the actual coefficient map. -/
theorem modelDiagramTwoChartSequenceMap_middle {b : Under R} (g : a ⟶ b) (d : ℤ) :
    (modelDiagramTwoChartSequenceMap F i g d).τ₂ =
      (stableHomotopyFunctor d).map
        (((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
          (modelDiagramTwoChartDiagram F i)).map g) := rfl

end KTheory.Bass
