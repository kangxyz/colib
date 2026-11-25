/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedCarrierDesc
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityPositiveSupport

/-!
# The actual raw-post evaluation seed carrier map

The original geometric positive square supplies the first half of each image cylinder;
the actual target cylinder supplies its second half. The two complete attachment equations
retain the ordinary and original unit-shifted sheets, with their separate tips. No native
continuity on the whole reference nerve is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen SmallWaldhausenCategory AlgebraicGeometry.RingedSpace SSet
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostMap
open GlobalSectionChangeIndex CommonReferenceNerve CutOpenCarrier InputSeedPostNodes
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
local notation "F" => InputSeedEvaluationCarrier.polyRef Y
local notation "J" => InputSeedEvaluationCarrier.chart Y
local notation "G" => InputSeedEvaluationCarrier.laurentRef Y
local notation "F'" => InputSeedCarrier.polyRef g
local notation "J'" => InputSeedCarrier.chart (X := X)
local notation "G'" => InputSeedCarrier.laurentRef g
local notation "ε₀" => InputSeedEvaluationCarrier.ordinary Y
local notation "ε₁" => InputSeedEvaluationCarrier.shifted Y
local notation "η₀" => InputSeedCarrier.ordinary g
local notation "η₁" => InputSeedCarrier.shifted g

/-- The original polynomial carrier follows actual normalized polynomial pullback. -/
def polynomialMap : C(|parameterSSet F|, |parameterSSet F'|) :=
  mapParameter (polynomialNode g)

/-- The whole Laurent carrier follows its original raw-post reference. -/
def laurentMap : C(|parameterSSet G|, |parameterSSet G'|) :=
  mapParameter (InputMixedDesc.postNode g)

/-- The chosen original source attachment retains its full unit-shifted anchor. -/
def originalAttachNode (e : Bool) : Node F → Node G :=
  attachPostcompNode F J G (if e then ε₁ else ε₀)

/-- The target attachment uses the corresponding distinct target sheet. -/
def targetAttachNode (e : Bool) : Node F' → Node G' :=
  attachPostcompNode F' J' G' (if e then η₁ else η₀)

/-- The first half of each image cylinder is the same original raw square parameter. -/
def squareParameter (e : Bool) : C(|parameterSSet F| × I, |parameterSSet G'|) :=
  if e then (mapParameter (ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g))).comp
    (InputSeedPostProduct.parameter g)
  else InputSeedPostProduct.parameter g

private theorem source_node (e : Bool) (N : Node F) :
    (if e then ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
      (InputSeedPostProduct.productNode g N 2) else InputSeedPostProduct.productNode g N 2) =
      InputMixedDesc.postNode g (originalAttachNode (Y := Y) e N) := by
  cases e
  · exact ordinary_source g N
  · exact shifted_source g N

private theorem target_node (e : Bool) (N : Node F) :
    (if e then ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g)
      (InputSeedPostProduct.productNode g N 4) else InputSeedPostProduct.productNode g N 4) =
      targetAttachNode g e (polynomialNode g N) := by
  cases e
  · exact ordinary_target g N
  · exact shifted_target g N

/-- Every original polynomial point has its full raw-post source attachment. -/
theorem square_zero (e : Bool) (y : |parameterSSet F|) :
    squareParameter g e (y, 0) =
      laurentMap g (mapParameter (originalAttachNode (Y := Y) e) y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  cases e
  · change InputSeedPostProduct.parameter g (_, 0) = _
    rw [InputSeedPostProduct.parameter_zero, mapParameter_parameter]
    change parameter G' _ z = mapParameter _ (mapParameter _ (parameter F N z))
    rw [mapParameter_parameter, mapParameter_parameter]
    exact congrArg (fun M => parameter G' M z) (funext fun i => source_node g false (N i))
  · change mapParameter _ (InputSeedPostProduct.parameter g (_, 0)) = _
    rw [InputSeedPostProduct.parameter_zero, mapParameter_parameter, mapParameter_parameter]
    change parameter G' _ z = mapParameter _ (mapParameter _ (parameter F N z))
    rw [mapParameter_parameter, mapParameter_parameter]
    exact congrArg (fun M => parameter G' M z) (funext fun i => source_node g true (N i))

/-- The full terminal square column is precisely the actual target cylinder attachment. -/
theorem square_one (e : Bool) (y : |parameterSSet F|) :
    squareParameter g e (y, 1) =
      mapParameter (targetAttachNode g e) (polynomialMap g y) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  cases e
  · change InputSeedPostProduct.parameter g (_, 1) = _
    rw [InputSeedPostProduct.parameter_one, mapParameter_parameter]
    change parameter G' _ z = mapParameter _ (mapParameter _ (parameter F N z))
    rw [mapParameter_parameter, mapParameter_parameter]
    exact congrArg (fun M => parameter G' M z) (funext fun i => target_node g false (N i))
  · change mapParameter _ (InputSeedPostProduct.parameter g (_, 1)) = _
    rw [InputSeedPostProduct.parameter_one, mapParameter_parameter, mapParameter_parameter]
    change parameter G' _ z = mapParameter _ (mapParameter _ (parameter F N z))
    rw [mapParameter_parameter, mapParameter_parameter]
    exact congrArg (fun M => parameter G' M z) (funext fun i => target_node g true (N i))

/-- The actual Laurent cell of the descended map. -/
def laurentCell : C(|parameterSSet G|, InputSeedCarrier.Carrier g) :=
  (laurentInclusion F' J' G' η₀ η₁).comp (laurentMap g)

/-- The original source of the selected full image cylinder. -/
def sourceCell (e : Bool) : C(|parameterSSet F|, InputSeedCarrier.Carrier g) :=
  (laurentCell g).comp (mapParameter (originalAttachNode (Y := Y) e))

/-- The target raw square endpoint is the selected actual cylinder attachment. -/
def middleCell (e : Bool) : C(|parameterSSet F|, InputSeedCarrier.Carrier g) :=
  (laurentInclusion F' J' G' η₀ η₁).comp
    ((mapParameter (targetAttachNode g e)).comp (polynomialMap g))

/-- The two image cylinders keep separate tips. -/
def tip (e : Bool) : InputSeedCarrier.Carrier g :=
  if e then tipPlus F' J' G' η₀ η₁ else tipMinus F' J' G' η₀ η₁

/-- The original raw square on the selected complete unit sheet. -/
def rawHalf (e : Bool) : (sourceCell g e).Homotopy (middleCell g e) where
  toFun z := laurentInclusion F' J' G' η₀ η₁ (squareParameter g e (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left y := congrArg (laurentInclusion F' J' G' η₀ η₁) (square_zero g e y)
  map_one_left y := congrArg (laurentInclusion F' J' G' η₀ η₁) (square_one g e y)

/-- The second half retains the target's actual polynomial cylinder and its original height. -/
def targetCylinder (e : Bool) :
    (middleCell g e).Homotopy (ContinuousMap.const _ (tip g e)) where
  toFun z := (if e then cylinderPlus F' J' G' η₀ η₁ else
    cylinderMinus F' J' G' η₀ η₁) (polynomialMap g z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left y := by
    cases e
    · exact cylinderMinus_zero F' J' G' η₀ η₁ (polynomialMap g y)
    · exact cylinderPlus_zero F' J' G' η₀ η₁ (polynomialMap g y)
  map_one_left y := by
    cases e
    · exact cylinderMinus_one F' J' G' η₀ η₁ (polynomialMap g y)
    · exact cylinderPlus_one F' J' G' η₀ η₁ (polynomialMap g y)

/-- The original raw-square half precedes the unchanged target-cylinder half. -/
def cylinderCell (e : Bool) : C(|parameterSSet F| × I, InputSeedCarrier.Carrier g) :=
  ((rawHalf g e).trans (targetCylinder g e)).toContinuousMap.comp
    ⟨Prod.swap, continuous_swap⟩

/-- The complete source attachment is preserved by both original image cylinders. -/
theorem cylinder_zero (e : Bool) (y : |parameterSSet F|) :
    cylinderCell g e (y, 0) = sourceCell g e y :=
  ((rawHalf g e).trans (targetCylinder g e)).apply_zero y

/-- Each whole terminal edge is its corresponding separate tip. -/
theorem cylinder_one (e : Bool) (y : |parameterSSet F|) :
    cylinderCell g e (y, 1) = tip g e :=
  ((rawHalf g e).trans (targetCylinder g e)).apply_one y

/-- The actual raw-post carrier map descends from the original two complete cylinders. -/
def map : InputSeedEvaluationCarrier.Carrier Y ⟶ InputSeedCarrier.Carrier g :=
  InputSeedCarrierDesc.map F J G ε₀ ε₁ (InputSeedCarrier.Carrier g)
    (laurentCell g) (cylinderCell g false) (cylinderCell g true)
    (tip g false) (tip g true) (cylinder_zero g false) (cylinder_one g false)
    (cylinder_zero g true) (cylinder_one g true)

/-- Every Laurent point follows its original raw pullback cell. -/
theorem map_laurent (y : |parameterSSet G|) :
    map g (laurentInclusion F J G ε₀ ε₁ y) = laurentCell g y :=
  InputSeedCarrierDesc.map_laurent F J G ε₀ ε₁ (InputSeedCarrier.Carrier g)
    (laurentCell g) (cylinderCell g false) (cylinderCell g true)
    (tip g false) (tip g true) (cylinder_zero g false) (cylinder_one g false)
    (cylinder_zero g true) (cylinder_one g true) y

/-- Every ordinary cylinder point retains the two original raw-map half clocks. -/
theorem map_cylinderMinus (y : |parameterSSet F|) (s : I) :
    map g (cylinderMinus F J G ε₀ ε₁ (y, s)) = cylinderCell g false (y, s) :=
  InputSeedCarrierDesc.map_cylinderMinus F J G ε₀ ε₁ (InputSeedCarrier.Carrier g)
    (laurentCell g) (cylinderCell g false) (cylinderCell g true)
    (tip g false) (tip g true) (cylinder_zero g false) (cylinder_one g false)
    (cylinder_zero g true) (cylinder_one g true) y s

/-- Every shifted cylinder point retains its own original unit sheet and both half clocks. -/
theorem map_cylinderPlus (y : |parameterSSet F|) (s : I) :
    map g (cylinderPlus F J G ε₀ ε₁ (y, s)) = cylinderCell g true (y, s) :=
  InputSeedCarrierDesc.map_cylinderPlus F J G ε₀ ε₁ (InputSeedCarrier.Carrier g)
    (laurentCell g) (cylinderCell g false) (cylinderCell g true)
    (tip g false) (tip g true) (cylinder_zero g false) (cylinder_one g false)
    (cylinder_zero g true) (cylinder_one g true) y s

/-- The ordinary source tip is the ordinary target tip. -/
theorem map_tipMinus : map g (tipMinus F J G ε₀ ε₁) = tip g false :=
  InputSeedCarrierDesc.map_tipMinus F J G ε₀ ε₁ (InputSeedCarrier.Carrier g)
    (laurentCell g) (cylinderCell g false) (cylinderCell g true)
    (tip g false) (tip g true) (cylinder_zero g false) (cylinder_one g false)
    (cylinder_zero g true) (cylinder_one g true)

/-- The shifted source tip stays distinct as the shifted target tip. -/
theorem map_tipPlus : map g (tipPlus F J G ε₀ ε₁) = tip g true :=
  InputSeedCarrierDesc.map_tipPlus F J G ε₀ ε₁ (InputSeedCarrier.Carrier g)
    (laurentCell g) (cylinderCell g false) (cylinderCell g true)
    (tip g false) (tip g true) (cylinder_zero g false) (cylinder_one g false)
    (cylinder_zero g true) (cylinder_one g true)

private theorem pointwise_attachPostcomp
    {V W T : WideSubcategory preservesZero.{u}}
    (f : V ⟶ W) (j : W ⟶ T) (k : V ⟶ T)
    (ε : k.hom.toFunctor ≅ (f ≫ j).hom.toFunctor) (n : ℕ)
    (y : |parameterSSet f|) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily k n (mapParameter (attachPostcompNode f j k ε) y) x =
      (prespectrumMap j).map n (pointwisePrespectrumFamily f n y x) := by
  obtain ⟨m, N, z, rfl⟩ := exists_parameter f y
  rw [mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact simplexFamily_attachPostcomp f j k ε N n z x

/-- Whole polynomial evaluation follows the actual raw polynomial map. -/
theorem polynomial_native (n : ℕ) (y : |parameterSSet F|)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    pointwisePrespectrumFamily F' n (polynomialMap g y) x =
      (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g)).map n
        (pointwisePrespectrumFamily F n y x) :=
  pointwise_attachPostcomp F (evaluationRawMap (polynomial.map g)) F'
    (polynomialSourceIso g) n y x

/-- Whole Laurent evaluation follows the actual raw Laurent map. -/
theorem laurent_native (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    pointwisePrespectrumFamily G' n (laurentMap g y) x =
      (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g)).map n
        (pointwisePrespectrumFamily G n y x) :=
  pointwise_attachPostcomp G (evaluationRawMap (laurent.map g)) G'
    (InputMixedDesc.postSourceIso g) n y x

/-- Both separately anchored square sheets recover the same original geometric raw square. -/
theorem square_native (e : Bool) (n : ℕ) (y : |parameterSSet F|) (r : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    pointwisePrespectrumFamily G' n (squareParameter g e (y, r)) x =
      (GlobalRawBass.plusSquareHomotopy g).level n
        (r, pointwisePrespectrumFamily F n y x) := by
  cases e
  · exact InputSeedPostProduct.native g n y r x
  · change pointwisePrespectrumFamily G' n
      (mapParameter _ (InputSeedPostProduct.parameter g (y, r))) x = _
    rw [pointwise_reanchor]
    exact InputSeedPostProduct.native g n y r x

/-- The first native half is the entire original square followed by Laurent inclusion. -/
theorem rawHalf_native (e : Bool) (n : ℕ) (y : |parameterSSet F|) (r : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval F' J' G' η₀ η₁ n (rawHalf g e (r, y)) x =
      ((GlobalRawBass.plusSquareHomotopy g).postcomp
        (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))).level n
          (r, pointwisePrespectrumFamily F n y x) := by
  change nativeEval F' J' G' η₀ η₁ n
    (laurentInclusion F' J' G' η₀ η₁ (squareParameter g e (y, r))) x = _
  rw [nativeEval_laurentInclusion, square_native]; rfl

/-- The second native half is the unchanged target cylinder on the actual polynomial image. -/
theorem targetCylinder_native (e : Bool) (n : ℕ) (y : |parameterSSet F|) (r : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval F' J' G' η₀ η₁ n (targetCylinder g e (r, y)) x =
      (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
        (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).level n
          (r, pointwisePrespectrumFamily F n y x) := by
  cases e
  · change nativeEval F' J' G' η₀ η₁ n
      (cylinderMinus F' J' G' η₀ η₁ (polynomialMap g y, r)) x = _
    rw [nativeEval_cylinderMinus, polynomial_native]; rfl
  · change nativeEval F' J' G' η₀ η₁ n
      (cylinderPlus F' J' G' η₀ η₁ (polynomialMap g y, r)) x = _
    rw [nativeEval_cylinderPlus, polynomial_native]; rfl

/-- Every cylinder height recovers the original raw cone-map null with its literal half cut. -/
theorem cylinder_native (e : Bool) (n : ℕ) (y : |parameterSSet F|) (r : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval F' J' G' η₀ η₁ n (cylinderCell g e (y, r)) x =
      (mappingConeSquareNullHomotopy (GlobalRawBass.InputIdentityPositive.chart Y)
        (GlobalRawBass.InputIdentityPositive.chart X)
        (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
        (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
        (GlobalRawBass.plusSquareHomotopy g)).level n
          (r, pointwisePrespectrumFamily F n y x) := by
  change nativeEval F' J' G' η₀ η₁ n
    (((rawHalf g e).trans (targetCylinder g e)) (r, y)) x = _
  rw [mappingConeSquareNullHomotopy, ContinuousMap.Homotopy.trans_apply]
  change _ =
    ((((GlobalRawBass.plusSquareHomotopy g).postcomp
        (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X))).levelHomotopy n).trans
      ((Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
        (mappingConeHomotopy (GlobalRawBass.InputIdentityPositive.chart X))).levelHomotopy n))
      (r, pointwisePrespectrumFamily F n y x)
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact rawHalf_native g e n y _ x
  · exact targetCylinder_native g e n y _ x

/-- The complete descended map is the original raw positive cone input on every native value. -/
theorem native (n : ℕ) (y : InputSeedEvaluationCarrier.Carrier Y)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval F' J' G' η₀ η₁ n (map g y) x =
      (GlobalRawBass.InputIdentityPositive.coneMap g).map n
        (nativeEval F J G ε₀ ε₁ n y x) := by
  rcases exists_native_cell F J G ε₀ ε₁ y with
    ⟨z, rfl⟩ | ⟨z, r, rfl⟩ | ⟨z, r, rfl⟩ | rfl | rfl
  · rw [map_laurent]
    change nativeEval F' J' G' η₀ η₁ n
      (laurentInclusion F' J' G' η₀ η₁ (laurentMap g z)) x =
        (GlobalRawBass.InputIdentityPositive.coneMap g).map n
          (nativeEval F J G ε₀ ε₁ n (laurentInclusion F J G ε₀ ε₁ z) x)
    rw [nativeEval_laurentInclusion, nativeEval_laurentInclusion, laurent_native]; rfl
  · rw [map_cylinderMinus, nativeEval_cylinderMinus, cylinder_native]; rfl
  · rw [map_cylinderPlus, nativeEval_cylinderPlus, cylinder_native]; rfl
  · exact (congrArg (fun z => nativeEval F' J' G' η₀ η₁ n z x)
      (map_tipMinus g)).trans
      ((nativeEval_tipMinus F' J' G' η₀ η₁ n x).trans
        (((GlobalRawBass.InputIdentityPositive.coneMap g).map_point n).symm.trans
          (congrArg ((GlobalRawBass.InputIdentityPositive.coneMap g).map n)
            (nativeEval_tipMinus F J G ε₀ ε₁ n x).symm)))
  · exact (congrArg (fun z => nativeEval F' J' G' η₀ η₁ n z x)
      (map_tipPlus g)).trans
      ((nativeEval_tipPlus F' J' G' η₀ η₁ n x).trans
        (((GlobalRawBass.InputIdentityPositive.coneMap g).map_point n).symm.trans
          (congrArg ((GlobalRawBass.InputIdentityPositive.coneMap g).map n)
            (nativeEval_tipPlus F J G ε₀ ε₁ n x).symm)))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostMap
