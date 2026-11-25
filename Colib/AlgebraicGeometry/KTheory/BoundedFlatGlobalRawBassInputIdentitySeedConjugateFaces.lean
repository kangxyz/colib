/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedIdentityNullFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedIdentityUnitProducts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedConjugation
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenSurfaceBoundary

/-!
# The prescribed identity seed families and their exact carrier route

The two actual null sheets and the original six-node unit products form the literal
null-inverse, unit, null words. Their initial paths are the fixed old and new seed words,
and their entire terminal paths agree before evaluation. The right route retains the
left-associated target identity, constant terminal seed, reversed source identity word.
Both tips and both independent route and seed clocks remain separate.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedConjugateFaces
open CommonReferenceNerve InputIdentitySeedCarrier
variable (X : Scheme.{u})

/-- The original target null family, with null time first for literal path concatenation. -/
def targetNull (e : Bool) : (InputIdentitySeedIdentityNullFaces.targetEdge X e).Homotopy
    (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) e)) :=
  (InputIdentitySeedIdentityNullFaces.targetFirst X e).trans
    (InputIdentitySeedIdentityNullFaces.targetLast X e)

/-- The source null family retains the same path-time-first convention. -/
def sourceNull (e : Bool) : (InputIdentitySeedIdentityNullFaces.sourceEdge X e).Homotopy
    (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) e)) :=
  (InputIdentitySeedIdentityNullFaces.sourceFirst X e).trans
    (InputIdentitySeedIdentityNullFaces.sourceLast X e)

/-- The actual target scalar edge joins the moving starts of the two target null sheets. -/
def targetUnit : (InputIdentitySeedIdentityNullFaces.targetEdge X false).Homotopy
    (InputIdentitySeedIdentityNullFaces.targetEdge X true) where
  toFun z := InputIdentitySeedIdentityUnitProducts.target X (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := InputIdentitySeedIdentityUnitProducts.target_zero X r
  map_one_left r := InputIdentitySeedIdentityUnitProducts.target_one X r

/-- The actual source scalar edge joins the different moving source-identity endpoints. -/
def sourceUnit : (InputIdentitySeedIdentityNullFaces.sourceEdge X false).Homotopy
    (InputIdentitySeedIdentityNullFaces.sourceEdge X true) where
  toFun z := InputIdentitySeedIdentityUnitProducts.source X (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := InputIdentitySeedIdentityUnitProducts.source_zero X r
  map_one_left r := InputIdentitySeedIdentityUnitProducts.source_one X r

/-- The target seed word has the original right-nested unit and positive-null subdivision. -/
def targetWordFamily : (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) false)).Homotopy
    (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) true)) :=
  (targetNull X false).symm.trans ((targetUnit X).trans (targetNull X true))

/-- The source seed word uses its own unit product and the unchanged source-null family. -/
def sourceWordFamily : (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) false)).Homotopy
    (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) true)) :=
  (sourceNull X false).symm.trans ((sourceUnit X).trans (sourceNull X true))

/-- Target identity time and the whole seed path time are independent coordinates. -/
def target : C(I × I, Carrier (𝟙 X)) :=
  ⟨fun z ↦ targetWordFamily X (z.2, z.1), by fun_prop⟩

/-- The source identity family retains the same original seed-time association. -/
def source : C(I × I, Carrier (𝟙 X)) :=
  ⟨fun z ↦ sourceWordFamily X (z.2, z.1), by fun_prop⟩

/-- Every target seed starts at the actual ordinary sheet tip. -/
theorem target_zero (r : I) :
    target X (r, 0) = InputIdentitySeedCone.tip (𝟙 X) false :=
  (targetWordFamily X).apply_zero r

/-- Every target seed ends at its distinct shifted sheet tip. -/
theorem target_one (r : I) :
    target X (r, 1) = InputIdentitySeedCone.tip (𝟙 X) true :=
  (targetWordFamily X).apply_one r

/-- The whole source seed begins at that same ordinary tip. -/
theorem source_zero (r : I) :
    source X (r, 0) = InputIdentitySeedCone.tip (𝟙 X) false :=
  (sourceWordFamily X).apply_zero r

/-- The whole source seed keeps the separate shifted terminal tip. -/
theorem source_one (r : I) :
    source X (r, 1) = InputIdentitySeedCone.tip (𝟙 X) true :=
  (sourceWordFamily X).apply_one r

/-- At each target identity time the actual conjugate remains a path between the two tips. -/
def targetPath (r : I) : Path (InputIdentitySeedCone.tip (𝟙 X) false)
    (InputIdentitySeedCone.tip (𝟙 X) true) where
  toFun s := target X (r, s)
  continuous_toFun := by fun_prop
  source' := target_zero X r
  target' := target_one X r

/-- At each source identity time the complete source conjugate has those same two endpoints. -/
def sourcePath (r : I) : Path (InputIdentitySeedCone.tip (𝟙 X) false)
    (InputIdentitySeedCone.tip (𝟙 X) true) where
  toFun s := source X (r, s)
  continuous_toFun := by fun_prop
  source' := source_zero X r
  target' := source_one X r

/-- Taking the target path retains both original coordinates literally. -/
theorem targetPath_apply (r s : I) : targetPath X r s = target X (r, s) := rfl

/-- Taking the source path retains both original coordinates literally. -/
theorem sourcePath_apply (r s : I) : sourcePath X r s = source X (r, s) := rfl

/-- The entire target entrance is the unchanged old seed word, including both nested cuts. -/
theorem target_initial (s : I) :
    target X (0, s) = InputIdentitySeedConjugation.sourceWord (𝟙 X) s := by
  change ((targetNull X false).symm.trans ((targetUnit X).trans (targetNull X true))) (s, 0) =
    ((InputIdentitySeedNull.oldNull (𝟙 X) false).symm.trans
      ((InputIdentitySeedConjugation.oldUnit (𝟙 X)).trans
        (InputIdentitySeedNull.oldNull (𝟙 X) true))) s
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact InputIdentitySeedIdentityNullFaces.target_initial X false _
  · rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · exact InputIdentitySeedIdentityUnitProducts.target_initial X _
    · exact InputIdentitySeedIdentityNullFaces.target_initial X true _

/-- The entire source entrance is the fixed new seed, with its original unit and null paths. -/
theorem source_initial (s : I) :
    source X (0, s) = InputIdentitySeedConjugation.targetWord (𝟙 X) s := by
  change ((sourceNull X false).symm.trans ((sourceUnit X).trans (sourceNull X true))) (s, 0) =
    ((InputIdentitySeedNull.newNull (𝟙 X) false).symm.trans
      ((InputIdentitySeedConjugation.newUnit (𝟙 X)).trans
        (InputIdentitySeedNull.newNull (𝟙 X) true))) s
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact InputIdentitySeedIdentityNullFaces.source_initial X false _
  · rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split
    · exact InputIdentitySeedIdentityUnitProducts.source_initial X _
    · exact InputIdentitySeedIdentityNullFaces.source_initial X true _

/-- Both original identity families have the same complete terminal seed path. -/
theorem terminal (s : I) : target X (1, s) = source X (1, s) := by
  change ((targetNull X false).symm.trans ((targetUnit X).trans (targetNull X true))) (s, 1) =
    ((sourceNull X false).symm.trans ((sourceUnit X).trans (sourceNull X true))) (s, 1)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact InputIdentitySeedIdentityNullFaces.terminal X false _
  · rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split
    · exact (InputIdentitySeedIdentityUnitProducts.terminal X _).symm
    · exact InputIdentitySeedIdentityNullFaces.terminal X true _

/-- The actual common terminal seed still runs between the two different carrier tips. -/
def terminalPath : Path (InputIdentitySeedCone.tip (𝟙 X) false)
    (InputIdentitySeedCone.tip (𝟙 X) true) where
  toFun s := target X (1, s)
  continuous_toFun := by fun_prop
  source' := target_zero X 1
  target' := target_one X 1

/-- The target seed family is an actual whole-path homotopy from the original old seed. -/
def targetComparison : (InputIdentitySeedConjugation.sourceWord (𝟙 X)).Homotopy
    (terminalPath X) where
  toFun := target X
  continuous_toFun := (target X).continuous
  map_zero_left := target_initial X
  map_one_left _ := rfl
  prop' r s hs := by
    rcases hs with hs | hs
    · subst s
      exact (target_zero X r).trans (InputIdentitySeedConjugation.sourceWord (𝟙 X)).source.symm
    · subst s
      exact (target_one X r).trans (InputIdentitySeedConjugation.sourceWord (𝟙 X)).target.symm

/-- The source seed family reaches that exact common path before any native evaluation. -/
def sourceComparison : (InputIdentitySeedConjugation.targetWord (𝟙 X)).Homotopy
    (terminalPath X) where
  toFun := source X
  continuous_toFun := (source X).continuous
  map_zero_left := source_initial X
  map_one_left s := (terminal X s).symm
  prop' r s hs := by
    rcases hs with hs | hs
    · subst s
      exact (source_zero X r).trans (InputIdentitySeedConjugation.targetWord (𝟙 X)).source.symm
    · subst s
      exact (source_one X r).trans (InputIdentitySeedConjugation.targetWord (𝟙 X)).target.symm

/-- The right route retains the original quarter, quarter, and final-half time cuts. -/
def rightComparison : (InputIdentitySeedConjugation.sourceWord (𝟙 X)).Homotopy
    (InputIdentitySeedConjugation.targetWord (𝟙 X)) :=
  ((targetComparison X).trans (Path.Homotopy.refl (terminalPath X))).trans
    (sourceComparison X).symm

/-- The actual right surface keeps route time separate from the unchanged seed path time. -/
def right : C(I × I, Carrier (𝟙 X)) := (rightComparison X).toContinuousMap

/-- The prescribed right surface starts on the full original old seed. -/
theorem right_start (s : I) : right X (0, s) = InputIdentitySeedConjugation.sourceWord (𝟙 X) s :=
  (rightComparison X).apply_zero s

/-- Its final whole path is the fixed original new seed. -/
theorem right_finish (s : I) : right X (1, s) = InputIdentitySeedConjugation.targetWord (𝟙 X) s :=
  (rightComparison X).apply_one s

/-- Every right-route time fixes the ordinary tip independently of the seed coordinate. -/
theorem right_zero (r : I) : right X (r, 0) = InputIdentitySeedCone.tip (𝟙 X) false :=
  (rightComparison X).source r

/-- Every right-route time keeps the distinct shifted tip fixed. -/
theorem right_one (r : I) : right X (r, 1) = InputIdentitySeedCone.tip (𝟙 X) true :=
  (rightComparison X).target r

/-- The actual two routes produce all six full faces and all twelve whole edge seams. -/
def surfaces : CutOpenCarrier.RouteSurfaces (polyRef (𝟙 X)) (chart (X := X))
    (laurentRef (𝟙 X)) (ordinary (𝟙 X)) (shifted (𝟙 X)) where
  left := (InputIdentitySeedConjugation.comparison (𝟙 X)).toContinuousMap
  right := right X
  start := (InputIdentitySeedConjugation.sourceWord (𝟙 X)).toContinuousMap
  finish := (InputIdentitySeedConjugation.targetWord (𝟙 X)).toContinuousMap
  left_start := InputIdentitySeedConjugation.comparison_source (𝟙 X)
  left_finish := InputIdentitySeedConjugation.comparison_target (𝟙 X)
  right_start := right_start X
  right_finish := right_finish X
  left_zero := InputIdentitySeedConjugation.comparison_zero (𝟙 X)
  left_one := InputIdentitySeedConjugation.comparison_one (𝟙 X)
  right_zero := right_zero X
  right_one := right_one X

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedConjugateFaces
