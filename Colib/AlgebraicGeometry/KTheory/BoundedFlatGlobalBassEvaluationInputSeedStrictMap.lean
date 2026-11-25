/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictAttachment
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenMap

/-!
# The actual strict-input evaluation seed carrier in the mixed carrier

Two proved complete attachment squares map both original cylinders. Every point keeps its
original height, its separate tip, and its original native input after base evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictMap
open GlobalSectionChangeIndex CommonReferenceNerve CutOpenCarrier
open InputSeedStrictAttachment
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
local notation "F" => InputSeedEvaluationCarrier.polyRef X
local notation "J" => InputSeedCarrier.chart (X := X)
local notation "G" => InputSeedEvaluationCarrier.laurentRef X
local notation "F'" => InputSeedCarrier.polyRef g
local notation "G'" => InputSeedCarrier.laurentRef g
local notation "ε₀" => InputSeedEvaluationCarrier.ordinary X
local notation "ε₁" => InputSeedEvaluationCarrier.shifted X
local notation "η₀" => InputSeedCarrier.ordinary g
local notation "η₁" => InputSeedCarrier.shifted g

/-- The original polynomial reference follows the actual strict input and its full reference. -/
def polynomialMap : |parameterSSet F| ⟶ |parameterSSet F'| :=
  SSet.toTop.map (nerveMap (Codiscrete.functorOfFun (polynomialNode g)))

/-- The original Laurent reference follows its full strict-precomposition anchor. -/
def laurentMap : |parameterSSet G| ⟶ |parameterSSet G'| :=
  SSet.toTop.map (nerveMap (Codiscrete.functorOfFun (laurentNode g)))

/-- The ordinary full attachment agrees before mapping either displayed cylinder. -/
theorem ordinary_square :
    SSet.toTop.map (attaching F J G ε₀) ≫ laurentMap g =
      polynomialMap g ≫ SSet.toTop.map (attaching F' J G' η₀) := by
  ext y
  exact ordinary_parameter g y

/-- The shifted attachment uses the original forward unit and its proved complete square. -/
theorem shifted_square :
    SSet.toTop.map (attaching F J G ε₁) ≫ laurentMap g =
      polynomialMap g ≫ SSet.toTop.map (attaching F' J G' η₁) := by
  ext y
  exact shifted_parameter g y

/-- The actual strict-input carrier map is defined by its two proved complete attachment squares. -/
def map : InputSeedEvaluationCarrier.Carrier X ⟶ InputSeedCarrier.Carrier g :=
  CutOpenMap.map F J G F' J G' ε₀ ε₁ η₀ η₁
    (polynomialMap g) (laurentMap g) (ordinary_square g) (shifted_square g)

/-- The original Laurent parameter retains its full total-evaluation anchor. -/
theorem map_laurent (y : |parameterSSet G|) :
    map g (laurentInclusion F J G ε₀ ε₁ y) =
      laurentInclusion F' J G' η₀ η₁ (laurentMap g y) :=
  CutOpenMap.map_laurent F J G F' J G' ε₀ ε₁ η₀ η₁
    (polynomialMap g) (laurentMap g) (ordinary_square g) (shifted_square g) y

/-- The ordinary cylinder retains its complete polynomial parameter and exact height. -/
theorem map_cylinderMinus (y : |parameterSSet F|) (s : I) :
    map g (cylinderMinus F J G ε₀ ε₁ (y, s)) =
      cylinderMinus F' J G' η₀ η₁ (polynomialMap g y, s) :=
  CutOpenMap.map_cylinderMinus F J G F' J G' ε₀ ε₁ η₀ η₁
    (polynomialMap g) (laurentMap g) (ordinary_square g) (shifted_square g) y s

/-- The shifted cylinder retains its distinct sheet and that same original height. -/
theorem map_cylinderPlus (y : |parameterSSet F|) (s : I) :
    map g (cylinderPlus F J G ε₀ ε₁ (y, s)) =
      cylinderPlus F' J G' η₀ η₁ (polynomialMap g y, s) :=
  CutOpenMap.map_cylinderPlus F J G F' J G' ε₀ ε₁ η₀ η₁
    (polynomialMap g) (laurentMap g) (ordinary_square g) (shifted_square g) y s

/-- The first original tip remains the first tip. -/
theorem map_tipMinus : map g (tipMinus F J G ε₀ ε₁) = tipMinus F' J G' η₀ η₁ :=
  CutOpenMap.map_tipMinus F J G F' J G' ε₀ ε₁ η₀ η₁
    (polynomialMap g) (laurentMap g) (ordinary_square g) (shifted_square g)

/-- The other original tip remains the other tip. -/
theorem map_tipPlus : map g (tipPlus F J G ε₀ ε₁) = tipPlus F' J G' η₀ η₁ :=
  CutOpenMap.map_tipPlus F J G F' J G' ε₀ ε₁ η₀ η₁
    (polynomialMap g) (laurentMap g) (ordinary_square g) (shifted_square g)

private theorem pointwise_precomp
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (R : V ⟶ W) (P : T ⟶ V)
    (R' : T ⟶ W) (e : R'.hom.toFunctor ≅ (P ≫ R).hom.toFunctor) (n : ℕ)
    (y : |parameterSSet R|) (x : (prespectrum T).space n) :
    pointwisePrespectrumFamily R' n (mapParameter (attachPrecompNode R P R' e) y) x =
      pointwisePrespectrumFamily R n y ((prespectrumMap P).map n x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter R y
  rw [← hz, mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact simplexFamily_attachPrecomp R P R' e N n z x

/-- Every polynomial parameter retains the native value at the actual strict input. -/
theorem polynomial_native (n : ℕ) (y : |parameterSSet F|)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    pointwisePrespectrumFamily F' n (polynomialMap g y) x =
      pointwisePrespectrumFamily F n y ((prespectrumMap
        (boundedAboveFlatGlobalSectionModelFunctor.map g.op)).map n x) :=
  pointwise_precomp F (boundedAboveFlatGlobalSectionModelFunctor.map g.op) F'
    (polynomialSourceIso g) n y x

/-- Every Laurent parameter keeps the original total comparison at that same native input. -/
theorem laurent_native (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    pointwisePrespectrumFamily G' n (laurentMap g y) x =
      pointwisePrespectrumFamily G n y ((prespectrumMap
        (boundedAboveFlatGlobalSectionModelFunctor.map g.op)).map n x) :=
  pointwise_precomp G (boundedAboveFlatGlobalSectionModelFunctor.map g.op) G'
    (InputMixedDesc.preSourceIso g) n y x

/-- The full two-tip carrier map retains the original strict source input at every level. -/
theorem native (n : ℕ) (y : InputSeedEvaluationCarrier.Carrier X)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval F' J G' η₀ η₁ n (map g y) x =
      nativeEval F J G ε₀ ε₁ n y ((prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map
        g.op)).map n x) := by
  rcases exists_native_cell F J G ε₀ ε₁ y with
    ⟨z, rfl⟩ | ⟨z, s, rfl⟩ | ⟨z, s, rfl⟩ | rfl | rfl
  · rw [map_laurent, nativeEval_laurentInclusion, nativeEval_laurentInclusion, laurent_native]
  · rw [map_cylinderMinus, nativeEval_cylinderMinus, nativeEval_cylinderMinus, polynomial_native]
  · rw [map_cylinderPlus, nativeEval_cylinderPlus, nativeEval_cylinderPlus, polynomial_native]
  · rw [map_tipMinus, nativeEval_tipMinus, nativeEval_tipMinus]
  · rw [map_tipPlus, nativeEval_tipPlus, nativeEval_tipPlus]

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictMap
