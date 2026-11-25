/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierCharts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityTopNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopContraction
public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftSquareOperations

/-!
# The complete original global span identity carrier face

The actual global twenty-five-node family retains both polynomial unit squares and the original
base-unit/projection product. The original moving-square and target-cylinder contractions are
lifted at every native time. Only their pure scalar clock is reused from the coefficient proof.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierTop
open BoundedFlatPerfectOriginalUnitSquareSimplex InputIdentityTopNodes
open BoundedFlatCoefficientBassUnitTop
local notation "Wₛ" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "PMap" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable (X : Scheme.{u})

/-- Five free nodes on each chart, followed by the full original fifteen-node middle grid. -/
def nodes (i : Fin 25) : Node X :=
  if h : i.val < 5 then plusNodes X ⟨i.val, by omega⟩ else
    if h' : i.val < 10 then minusNodes X ⟨i.val - 5, by omega⟩ else
      middleNodes X ⟨i.val - 10, by omega⟩

/-- The eight plus-chart node indices in the merged 25-node simplex. -/
def plusIndex (i : Fin 8) : Fin 25 :=
  ⟨if i.val < 5 then i.val else 5 * (i.val - 5) + 12, by split_ifs <;> omega⟩
/-- The eight minus-chart node indices in the merged 25-node simplex. -/
def minusIndex (i : Fin 8) : Fin 25 :=
  ⟨if i.val < 5 then i.val + 5 else 5 * (i.val - 5) + 14, by split_ifs <;> omega⟩
/-- The fifteen middle-grid node indices in the merged 25-node simplex. -/
def middleIndex (i : Fin 15) : Fin 25 := ⟨10 + i.val, by omega⟩

/-- The monotone face selecting the eight plus-chart nodes. -/
def plusFace : ⦋7⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨plusIndex, by
  intro i j h
  change (plusIndex i).val ≤ (plusIndex j).val
  dsimp [plusIndex]
  split_ifs <;> omega⟩
/-- The monotone face selecting the eight minus-chart nodes. -/
def minusFace : ⦋7⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨minusIndex, by
  intro i j h
  change (minusIndex i).val ≤ (minusIndex j).val
  dsimp [minusIndex]
  split_ifs <;> omega⟩
/-- The monotone face selecting the fifteen middle-grid nodes. -/
def middleFace : ⦋14⦌ ⟶ ⦋24⦌ := SimplexCategory.Hom.mk ⟨middleIndex, by
  intro i j h
  change 10 + i.val ≤ 10 + j.val
  omega⟩

theorem plus_nodes (i : Fin 8) : nodes X (plusFace.toOrderHom i) = plusNodes X i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (plus_shared X 0).symm
  · exact (plus_shared X 1).symm
  · exact (plus_shared X 2).symm

theorem minus_nodes (i : Fin 8) : nodes X (minusFace.toOrderHom i) = minusNodes X i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (minus_shared X 0).symm
  · exact (minus_shared X 1).symm
  · exact (minus_shared X 2).symm

theorem middle_nodes (i : Fin 15) :
    nodes X (middleFace.toOrderHom i) = middleNodes X i := by
  fin_cases i <;> rfl

/-- One actual simplex contains all three unchanged moving pieces, with the six joins shared. -/
def simplex : ModelSimplex (asSmallCategory (Wₛ X))
    (asSmallCategory (Wₛ (laurent.obj X))) 24 :=
  ModelSimplex.ofIsos (source X) (fun i ↦ (nodes X i).1) (fun i ↦ (nodes X i).2)

theorem plus_face : (simplex X).face plusFace =
    InputIdentityTopSimplex.plusSimplex X := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (plus_nodes X)).trans (plus_family X)

theorem minus_face : (simplex X).face minusFace =
    InputIdentityTopSimplex.minusSimplex X := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (minus_nodes X)).trans (minus_family X)

theorem middle_face : (simplex X).face middleFace =
    InputIdentityTopSimplex.middleSimplex X := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (middle_nodes X)).trans (middle_family X)

private theorem family_simplex_congr
  {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
    (S T : ModelSimplex V W k) (h : S = T) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1))) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily T n (z, x) :=
  congrArg (fun U ↦ prespectrumSimplexFamily U n (z, x)) h

private theorem family_parameter_congr
  {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (n : ℕ)
    (z w : StdSimplex ℝ (Fin (k + 1))) (h : z = w) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily S n (w, x) :=
  congrArg (fun v ↦ prespectrumSimplexFamily S n (v, x)) h

theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (Wₛ X)).space n) :
    prespectrumSimplexFamily (simplex X) n (plusParameter (r, s), x) =
      ((InputIdentity.polynomialSquare X).postcompose
        (PMap (plus.app X))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_face (simplex X) plusFace n
    (BoundedFlatPerfectOriginalUnitSquareSimplex.squareParameter (r, s)) x).trans ?_
  refine (family_simplex_congr _ _ (plus_face X) n _ x).trans ?_
  exact InputIdentityTopSimplex.plus_native X n r s x

theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (Wₛ X)).space n) :
    prespectrumSimplexFamily (simplex X) n (minusParameter (r, s), x) =
      ((InputIdentity.polynomialSquare X).postcompose
        (PMap (minus.app X))).level n (r, (s, x)) := by
  refine (prespectrumSimplexFamily_face (simplex X) minusFace n
    (BoundedFlatPerfectOriginalUnitSquareSimplex.squareParameter (r, s)) x).trans ?_
  refine (family_simplex_congr _ _ (minus_face X) n _ x).trans ?_
  exact InputIdentityTopSimplex.minus_native X n r s x

theorem middle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (Wₛ X)).space n) :
    prespectrumSimplexFamily (simplex X) n (middleParameter.{u} (r, s), x) =
      (comparison X).map n
        (HomotopyPushout.cylinder
          (PMap (projection.app X))
          (PMap (projection.app X)) n
          (s, (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x))) := by
  refine (prespectrumSimplexFamily_face (simplex X) middleFace n
    (InputIdentityTopSimplex.middleParameter.{u} (r, s)) x).trans ?_
  refine (family_simplex_congr _ _ (middle_face X) n _ x).trans ?_
  exact InputIdentityTopSimplex.middle_native X n r s x

/-- The prespectrum map induced by the global polynomial projection. -/
abbrev polynomialMap := PMap (projection.app X)
/-- The original global Bass-square comparison map. -/
abbrev comparisonMap := comparison X

/-- The unchanged native moving square, before its identity-cylinder contractions. -/
def movingNative := HomotopyPushout.identicalLegMovingSquare
  (polynomialMap X) (polynomialMap X)
  (polynomialSquareHomotopy (𝟙 X))
  (coneSquareIdentityTrack (polynomialMap X))
  (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X)
  (InputIdentity.polynomialHomotopy X)
  (InputIdentity.polynomialSquare X)

private theorem native_paste_value {E F : LoopPrespectrum.{u}}
    {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (J : H₀.Square H₁ L M) (K : K₀.Square K₁ M N)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.pastePaths K).level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        J.level n (r, (⟨2 * s,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else K.level n (r, (⟨2 * s - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  ContinuousMap.Homotopy.trans_apply _ _ _

private theorem mapped_paste_evaluate {d : ℕ} {U : Type*}
    {a₀ b₀ c₀ a₁ b₁ c₁ : StdSimplex ℝ (Fin (d + 1))}
    {p₀ : Path a₀ b₀} {p₁ : Path a₁ b₁} {q₀ : Path b₀ c₀} {q₁ : Path b₁ c₁}
    {l : Path a₀ a₁} {m : Path b₀ b₁} {j : Path c₀ c₁}
    {E F : LoopPrespectrum.{u}} {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
    {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
    (Q : ParameterSquare p₀ p₁ l m) (R : ParameterSquare q₀ q₁ m j)
    (J : H₀.Square H₁ L M) (K : K₀.Square K₁ M N) (n : ℕ) (x : E.space n)
    (e : StdSimplex ℝ (Fin (d + 1)) → U) (v : F.space n → U)
    (hQ : ∀ r s, e (Q.parameter (r, s)) = v (J.level n (r, (s, x))))
    (hR : ∀ r s, e (R.parameter (r, s)) = v (K.level n (r, (s, x))))
    (r s : unitInterval) :
    e ((Q.pastePaths R).parameter (r, s)) = v ((J.pastePaths K).level n (r, (s, x))) := by
  rw [ParameterSquare.pastePaths_apply, native_paste_value]
  split
  · exact hQ _ _
  · exact hR _ _

/-- All three pieces paste to the actual native moving square, before the original postmap. -/
theorem moving_native : SquareLift (simplex X) movingSquare.{u}
    ((movingNative X).postcompose (comparisonMap X)) := by
  intro n r s x
  change prespectrumSimplexFamily (simplex X) n (movingSquare.parameter (r, s), x) =
    (comparisonMap X).map n ((movingNative X).level n (r, (s, x)))
  unfold movingSquare movingNative HomotopyPushout.identicalLegMovingSquare
  refine mapped_paste_evaluate _ _ _ _ n x
    (fun z ↦ prespectrumSimplexFamily (simplex X) n (z, x))
    ((comparisonMap X).map n) ?_ ?_ r s
  · intro r s
    exact plus_native X n r s x
  · intro r s
    refine mapped_paste_evaluate _ _ _ _ n x
      (fun z ↦ prespectrumSimplexFamily (simplex X) n (z, x))
      ((comparisonMap X).map n) ?_ ?_ r s
    · intro r s
      exact middle_native X n r s x
    · intro r s
      exact minus_native X n r (unitInterval.symm s) x

/-- The unpaused original cylinder is the terminal row of the actual product grid. -/
theorem cylinder_native : PathLift (simplex X) middleEnd
    ((HomotopyPushout.glue (polynomialMap X) (polynomialMap X)).postcomp
      (comparisonMap X)) := by
  intro n s x
  refine (family_parameter_congr (simplex X) n _ _ (middleSquare.at_one s).symm x).trans ?_
  refine (middle_native X n 1 s x).trans ?_
  exact congrArg (fun y ↦ (comparisonMap X).map n
    (HomotopyPushout.cylinder (polynomialMap X) (polynomialMap X) n (s, y)))
    ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).at_one n x)

/-- The scalar terminal vertex is the exact target of the unchanged original cylinder. -/
theorem cylinder_target_native : PathLift (simplex X) (Path.refl (StdSimplex.single 24))
    ((Topology.LoopPrespectrum.Homotopy.refl ((polynomialMap X) ≫
      HomotopyPushout.inr (polynomialMap X) (polynomialMap X))).postcomp
      (comparisonMap X)) := by
  intro n t x
  refine (family_parameter_congr (simplex X) n _ _ middleEnd.target.symm x).trans ?_
  exact (cylinder_native X n 1 x).trans (congrArg ((comparisonMap X).map n)
    ((HomotopyPushout.glue (polynomialMap X) (polynomialMap X)).at_one n x))

/-- Both original constant pieces of the target cylinder contract with their exact native speeds. -/
theorem target_contraction_native : HomotopyLift (simplex X) targetContraction
    ((HomotopyPushout.identicalLegIdentityTargetComparison (polynomialMap X)).postcomp
      (comparisonMap X)) := by
  have h := cylinder_native X
  have hc := cylinder_target_native X
  have hp := PathLift.postcompTrans (simplex X) (comparisonMap X) h hc
  exact HomotopyLift.postcompTrans (simplex X) (comparisonMap X)
    (PathLift.postcompReflTrans (simplex X) (comparisonMap X) hp)
    (PathLift.postcompTransRefl (simplex X) (comparisonMap X) h)

/-- The whole left endpoint track of the moving square is the original polynomial unit. -/
theorem left_native : PathLift (simplex X) (binaryPath (k := 24) 2 3 22)
    ((Homotopy.precomp (polynomialMap X)
      ((InputIdentity.polynomialHomotopy X).postcomp
        (HomotopyPushout.inl (polynomialMap X) (polynomialMap X)))).postcomp
      (comparisonMap X)) := by
  intro n r x
  refine (family_parameter_congr (simplex X) n _ _ (plusSquare.left r).symm x).trans ?_
  refine (plus_native X n r 0 x).trans ?_
  exact congrArg ((PMap (plus.app X)).map n)
    ((InputIdentity.polynomialSquare X).left n r x)

/-- The whole right endpoint track retains the separate inverse Laurent chart. -/
theorem right_native : PathLift (simplex X) (binaryPath (k := 24) 7 8 24)
    ((Homotopy.precomp (polynomialMap X)
      ((InputIdentity.polynomialHomotopy X).postcomp
        (HomotopyPushout.inr (polynomialMap X) (polynomialMap X)))).postcomp
      (comparisonMap X)) := by
  intro n r x
  refine (family_parameter_congr (simplex X) n _ _
    ((unitFaceSquare minusFace).left r).symm x).trans ?_
  refine (minus_native X n r 0 x).trans ?_
  exact congrArg ((PMap (minus.app X)).map n)
    ((InputIdentity.polynomialSquare X).left n r x)

/-- Every point of the original polynomial-span identity cylinder after the unchanged Bass map
has this explicit common-simplex parameter. No span identity or comparison track is replaced. -/
theorem top_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (Wₛ X)).space n) :
    prespectrumSimplexFamily (simplex X) n (topParameter.{u} (r, t), x) =
      ((InputIdentity.spanHomotopy X).postcomp
        (comparison X)).level n
        (r, HomotopyPushout.cylinder (polynomialMap X) (polynomialMap X) n (t, x)) := by
  have hm : HomotopyLift (simplex X) movingSquare.{u}.toBoundary
      ((movingNative X).toBoundary.postcomp (comparisonMap X)) :=
    SquareLift.toBoundary (simplex X) (moving_native X)
  let L := Homotopy.precomp (polynomialMap X)
    ((InputIdentity.polynomialHomotopy X).postcomp
      (HomotopyPushout.inl (polynomialMap X) (polynomialMap X)))
  let M := Homotopy.precomp (polynomialMap X)
    ((InputIdentity.polynomialHomotopy X).postcomp
      (HomotopyPushout.inr (polynomialMap X) (polynomialMap X)))
  have hl : HomotopyLift (simplex X)
      (Path.Homotopy.refl (binaryPath (k := 24) 2 3 22))
      ((Homotopy.RelHomotopy.refl L).postcomp (comparisonMap X)) := by
    intro n r s x
    exact left_native X n s x
  have hr : HomotopyLift (simplex X)
      (Path.Homotopy.refl (binaryPath (k := 24) 7 8 24).symm)
      ((Homotopy.RelHomotopy.refl M.symm).postcomp (comparisonMap X)) := by
    intro n r s x
    exact right_native X n (unitInterval.symm s) x
  have hc := HomotopyLift.postcompHcomp (simplex X) (comparisonMap X)
    (HomotopyLift.postcompHcomp (simplex X) (comparisonMap X)
      hl (target_contraction_native X)) hr
  have h := HomotopyLift.postcompTrans (simplex X) (comparisonMap X) hm hc
  exact HomotopyLift.postcompOfBoundary (simplex X) (comparisonMap X) h n r t x



/-- The complete original top face lies in the same full reference carrier as the other faces. -/
def face : C(unitInterval × unitInterval, InputIdentityCarrierCharts.Carrier X) :=
  (CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)).comp
    BoundedFlatCoefficientBassUnitTop.topParameter.{u}

/-- Every native top-face point retains the specified unpaused span identity after comparison. -/
theorem face_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (Wₛ X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X) (face X)
        n ((r, t), x) =
      ((InputIdentity.spanHomotopy X).postcomp (comparison X)).level n
        (r, HomotopyPushout.cylinder
          (PMap (projection.app X))
          (PMap (projection.app X)) n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (InputIdentityNodes.source X)
    (face X) (nodes X) (r, t) (BoundedFlatCoefficientBassUnitTop.topParameter.{u} (r, t))
      rfl n x).trans ?_
  exact top_native X n r t x

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierTop
