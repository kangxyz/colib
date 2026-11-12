/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StrictSquareCofiberComparison
public import Colib.KTheory.Bass.ModelDiagramConnectivity

/-!
# Genuine Bass cofiber comparison for every finite original Model stage

The actual reduced span and unlooped cone retain all-point vanishing without a degree loss.
Their literal chosen points have the proved HEP, and their actual spaces are T1. Consequently
the original Bass cofiber comparison is stable for every map between squares of actual finite
Model-diagram stages. The common offset is the maximum of the two iteration indices; neither
connectivity hypotheses on later stages nor finite-stage stabilization are assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w}) (S : Arrow (Arrow C))

/-- The unchanged span and unlooped cone retain actual T1 separation. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramCofiberComparison.lean:29"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
instance modelDiagramSquareConeSpaceT1Space (m : ℕ) :
    T1Space ((mappingCone (StrictSquare.comparison
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj S))).space
        m) := by
  let T := ((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj S
  let : T1Space (T.left.left.space m) := modelDiagramIterateSpaceT1Space Q i F S.left.left m
  let : T1Space (T.left.right.space m) := modelDiagramIterateSpaceT1Space Q i F S.left.right m
  let : T1Space (T.right.left.space m) := modelDiagramIterateSpaceT1Space Q i F S.right.left m
  let : T1Space (T.right.right.space m) := modelDiagramIterateSpaceT1Space Q i F S.right.right m
  change T1Space ((mappingCone (StrictSquare.comparison T)).space m)
  infer_instance

/-- The actual unlooped square cone retains the original chosen-point HEP at every level. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramCofiberComparison.lean:42"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem modelDiagramSquareCone_point_homotopyExtensionProperty (m : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{w + 1}
      ((mappingCone (StrictSquare.comparison
        (((strictDiagramIterate Q i).obj
          (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj S))).point
          m))) :=
  StrictSquare.cone_point_homotopyExtensionProperty _ m
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F S.left.left m)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F S.left.right m)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F S.right.left m)
    (modelDiagramIterate_point_homotopyExtensionProperty Q i F S.right.right m)

/-- The original span and unlooped cone lose no degree of the proved finite-stage range. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramCofiberComparison.lean:55"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem modelDiagramSquareCone_homotopyGroup_subsingleton (m n : ℕ) (hm : n + i + 2 ≤ m)
    (x : (mappingCone (StrictSquare.comparison
      (((strictDiagramIterate Q i).obj
        (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj S))).space m)
    (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k
      ((mappingCone (StrictSquare.comparison
        (((strictDiagramIterate Q i).obj
          (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj S))).space m) x) := by
  let D := (strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)
  let T := D.mapArrow.mapArrow.obj S
  have hA := modelDiagramIterate_point_homotopyExtensionProperty Q i F S.left.left m
  have hB := modelDiagramIterate_point_homotopyExtensionProperty Q i F S.left.right m
  have hC := modelDiagramIterate_point_homotopyExtensionProperty Q i F S.right.left m
  have hD := modelDiagramIterate_point_homotopyExtensionProperty Q i F S.right.right m
  have hπA : ∀ y t, t < n + 2 →
      Subsingleton (HomotopyGroup.Pi t (T.left.left.space m) y) := by
    intro y t ht
    exact modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F S.left.left m
      (by omega) t (by omega) y
  have hπB : ∀ y t, t < n + 2 →
      Subsingleton (HomotopyGroup.Pi t (T.left.right.space m) y) := by
    intro y t ht
    exact modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F S.left.right m
      (by omega) t (by omega) y
  have hπC : ∀ y t, t < n + 2 →
      Subsingleton (HomotopyGroup.Pi t (T.right.left.space m) y) := by
    intro y t ht
    exact modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F S.right.left m
      (by omega) t (by omega) y
  have hπD : ∀ y t, t < n + 2 →
      Subsingleton (HomotopyGroup.Pi t (T.right.right.space m) y) := by
    intro y t ht
    exact modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F S.right.right m
      (by omega) t (by omega) y
  exact ReducedMappingCone.homotopyGroup_subsingleton
    ((StrictSquare.span T).point m) (T.right.right.point m) ((StrictSquare.comparison T).map m)
    ((StrictSquare.comparison T).map_point m)
    (StrictSquare.span_point_homotopyExtensionProperty T m hA hB hC) hD n
    (HomotopyPushout.homotopyGroup_subsingleton T.left.hom T.hom.left m n hA hB hC
      hπA hπB hπC) hπD x k hk

/-- The original Bass cofiber comparison is stable at arbitrary actual finite Model stages. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelDiagramCofiberComparison.lean:98"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem modelDiagramSquare_loopedConeCofiberComparison_isStableEquivalence
    (j : ℕ) (G : C ⥤ WideSubcategory preservesZero.{w}) (T : Arrow (Arrow C))
    (a : (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj S) ⟶
      (((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj T)) :
    IsStableEquivalence (StrictSquare.loopedConeCofiberComparison a) := by
  let : ∀ m, T1Space ((mappingCone (StrictSquare.comparison
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj S))).space
        m) := modelDiagramSquareConeSpaceT1Space Q i F S
  let : ∀ m, T1Space ((mappingCone (StrictSquare.comparison
      (((strictDiagramIterate Q j).obj (G ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj T))).space
        m) := modelDiagramSquareConeSpaceT1Space Q j G T
  apply StrictSquare.loopedConeCofiberComparison_isStableEquivalence_of_linearGrowth a (max i j)
  · exact modelDiagramSquareCone_point_homotopyExtensionProperty Q i F S
  · exact modelDiagramSquareCone_point_homotopyExtensionProperty Q j G T
  · intro n x k hk
    exact modelDiagramSquareCone_homotopyGroup_subsingleton Q i F S
      (n + max i j + 2) n (by omega) x k hk
  · intro n x k hk
    exact modelDiagramSquareCone_homotopyGroup_subsingleton Q j G T
      (n + max i j + 2) n (by omega) x k hk

end KTheory.Bass

