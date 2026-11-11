/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StrictSquareCofiberComparison
public import Colib.Topology.Prespectrum.StrictSquareMapHomotopy
public import Colib.Topology.Prespectrum.StrictSquareZeroMap
public import Colib.Topology.Prespectrum.ConeDescNaturality

/-!
# Original Bass cofiber descent and its prescribed whole null track

The four actual cone descents of a coefficient-natural whole null track form a strict square.
The genuine Bass image of this square factors the original cone descent through the actual
Bass cofiber comparison. Its null track is the unchanged moving-span, cone and loop action,
with only the original composition and zero endpoint equalities. No endpoint equality is
used as a substitute for the full specified cylinder.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable {S T U : Arrow (Arrow LoopPrespectrum.{u})}
    (a : S ⟶ T) (b : T ⟶ U) {z : S ⟶ U} (H : MapHomotopy (a ≫ b) z)
    (h00 : z.left.left = zeroHom S.left.left U.left.left)
    (h01 : z.left.right = zeroHom S.left.right U.left.right)
    (h10 : z.right.left = zeroHom S.right.left U.right.left)
    (h11 : z.right.right = zeroHom S.right.right U.right.right)

/-- The four original quotient cone descents form the same target square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberDescent.lean:38"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
def coneSquareDesc : coneSquare a ⟶ U :=
  Arrow.homMk
    (Arrow.homMk
      (mappingConeDesc a.left.left b.left.left (H.source.cast rfl h00))
      (mappingConeDesc a.left.right b.left.right (H.upper.cast rfl h01)) (by
        exact (mappingConeDesc_naturality (coneTopFace a) b.left.left b.left.right U.left.hom
          (H.source.cast rfl h00) (H.upper.cast rfl h01) b.left.w.symm
          (fun n r x ↦ (H.commUpper n r x).symm)).symm))
    (Arrow.homMk
      (mappingConeDesc a.right.left b.right.left (H.lower.cast rfl h10))
      (mappingConeDesc a.right.right b.right.right (H.target.cast rfl h11)) (by
        exact (mappingConeDesc_naturality (coneBottomFace a) b.right.left b.right.right
          U.right.hom (H.lower.cast rfl h10) (H.target.cast rfl h11) b.right.w.symm
          (fun n r x ↦ (H.commBottom n r x).symm)).symm)) (by
        apply Arrow.hom_ext
        · exact (mappingConeDesc_naturality (coneLeftFace a) b.left.left b.right.left U.hom.left
            (H.source.cast rfl h00) (H.lower.cast rfl h10)
            (congrArg (fun f ↦ f.left) b.w).symm
            (fun n r x ↦ (H.commLower n r x).symm)).symm
        · exact (mappingConeDesc_naturality (coneRightFace a) b.left.right b.right.right
            U.hom.right (H.upper.cast rfl h01) (H.target.cast rfl h11)
            (congrArg (fun f ↦ f.right) b.w).symm
            (fun n r x ↦ (H.commRight n r x).symm)).symm)

/-- Each target inclusion keeps the original map on its corner, giving the unchanged square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberDescent.lean:63"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem coneSquareInclusion_desc :
    coneSquareInclusion a ≫ coneSquareDesc a b H h00 h01 h10 h11 = b := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext <;> exact mappingConeInclusion_desc _ _ _

/-- The original Bass action on the specified whole null track, with literal endpoint casts. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberDescent.lean:68"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
def loopedConeNullHomotopy :
    Homotopy (strictSquareLoopedConeFunctor.map a ≫ strictSquareLoopedConeFunctor.map b)
      (zeroHom (strictSquareLoopedConeFunctor.obj S) (strictSquareLoopedConeFunctor.obj U)) :=
  H.looped.cast (strictSquareLoopedConeFunctor.map_comp a b)
    (strictSquareLoopedConeFunctor_map_eq_zero z h00 h01 h10 h11)

/-- The original Bass cofiber comparison factors the prescribed actual quotient descent. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareCofiberDescent.lean:75"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem loopedConeCofiberComparison_desc :
    loopedConeCofiberComparison a ≫
        strictSquareLoopedConeFunctor.map (coneSquareDesc a b H h00 h01 h10 h11) =
      mappingConeDesc (strictSquareLoopedConeFunctor.map a)
        (strictSquareLoopedConeFunctor.map b) (loopedConeNullHomotopy a b H h00 h01 h10 h11) := by
  apply mappingCone_hom_ext
  · rw [← Category.assoc, loopedConeCofiberComparison_inclusion,
      ← strictSquareLoopedConeFunctor.map_comp, coneSquareInclusion_desc,
      mappingConeInclusion_desc]
  · intro n r γ
    change Path ((mappingCone (comparison S)).point n)
      ((mappingCone (comparison S)).point n) at γ
    apply Path.ext
    funext t
    change (mappingConeMap (strictSquareComparisonFunctor.map
      (coneSquareDesc a b H h00 h01 h10 h11))).map n
        ((coneInterchangeIso a).hom.map n
          (ReducedMappingCone.cylinder ((mappingCone (comparison S)).point n)
            ((mappingCone (comparison T)).point n)
            ((mappingConeMap (strictSquareComparisonFunctor.map a)).map n) (r, γ t))) =
      H.cone.level n (r, γ t)
    induction γ t using Quot.inductionOn with
    | h v => cases v with
      | inl y => rfl
      | inr v =>
        rcases v with ⟨s, x⟩
        induction x using Quot.inductionOn with
        | h v => cases v with
          | inl v => cases v <;> rfl
          | inr v => rfl

end Topology.LoopPrespectrum.StrictSquare

