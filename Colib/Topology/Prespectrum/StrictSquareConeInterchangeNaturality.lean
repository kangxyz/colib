/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StrictSquareConeInterchange

/-!
# Naturality of original strict-square cofiber interchange

An actual cube between two strict square maps induces the unchanged four corner cone maps.
The finite cofiber interchange is natural for those maps on every original target and
cylinder stratum. This keeps all original cube equations and the two independent cone times.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable {S T S' T' : Arrow (Arrow LoopPrespectrum.{u})}
  {a : S ⟶ T} {b : S' ⟶ T'} (k : Arrow.mk a ⟶ Arrow.mk b)

/-- The original four corner squares of an actual cube act on the actual cofiber square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchangeNaturality.lean:28"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
def coneSquareMap : coneSquare a ⟶ coneSquare b :=
  let ll : Arrow.mk a.left.left ⟶ Arrow.mk b.left.left :=
    Arrow.homMk k.left.left.left k.right.left.left (congrArg (fun f ↦ f.left.left) k.w)
  let lr : Arrow.mk a.left.right ⟶ Arrow.mk b.left.right :=
    Arrow.homMk k.left.left.right k.right.left.right (congrArg (fun f ↦ f.left.right) k.w)
  let rl : Arrow.mk a.right.left ⟶ Arrow.mk b.right.left :=
    Arrow.homMk k.left.right.left k.right.right.left (congrArg (fun f ↦ f.right.left) k.w)
  let rr : Arrow.mk a.right.right ⟶ Arrow.mk b.right.right :=
    Arrow.homMk k.left.right.right k.right.right.right (congrArg (fun f ↦ f.right.right) k.w)
  Arrow.homMk
    (Arrow.homMk (f := (coneSquare a).left) (g := (coneSquare b).left)
      (mappingConeMap ll) (mappingConeMap lr) (by
        change mappingConeFunctor.map ll ≫ mappingConeFunctor.map (coneTopFace b) =
          mappingConeFunctor.map (coneTopFace a) ≫ mappingConeFunctor.map lr
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Arrow.hom_ext
        · exact k.left.left.w
        · exact k.right.left.w))
    (Arrow.homMk (f := (coneSquare a).right) (g := (coneSquare b).right)
      (mappingConeMap rl) (mappingConeMap rr) (by
        change mappingConeFunctor.map rl ≫ mappingConeFunctor.map (coneBottomFace b) =
          mappingConeFunctor.map (coneBottomFace a) ≫ mappingConeFunctor.map rr
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Arrow.hom_ext
        · exact k.left.right.w
        · exact k.right.right.w)) (by
      apply Arrow.hom_ext
      · change mappingConeFunctor.map ll ≫ mappingConeFunctor.map (coneLeftFace b) =
          mappingConeFunctor.map (coneLeftFace a) ≫ mappingConeFunctor.map rl
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Arrow.hom_ext
        · exact congrArg (fun f ↦ f.left) k.left.w
        · exact congrArg (fun f ↦ f.left) k.right.w
      · change mappingConeFunctor.map lr ≫ mappingConeFunctor.map (coneRightFace b) =
          mappingConeFunctor.map (coneRightFace a) ≫ mappingConeFunctor.map rr
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Arrow.hom_ext
        · exact congrArg (fun f ↦ f.right) k.left.w
        · exact congrArg (fun f ↦ f.right) k.right.w)

/-- The actual finite interchange commutes with every original strict cube. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchangeNaturality.lean:73"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem coneInterchangeIso_naturality :
    mappingConeMap ((strictSquareComparisonFunctor ⋙ mappingConeFunctor).mapArrow.map k) ≫
        (coneInterchangeIso b).hom =
      (coneInterchangeIso a).hom ≫
        mappingConeMap (strictSquareComparisonFunctor.map (coneSquareMap k)) := by
  apply mappingCone_hom_ext
  · apply mappingCone_hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s q
      induction q using Quot.inductionOn with
      | h z => cases z with
        | inl z => cases z <;> rfl
        | inr z => rfl
  · intro n r q
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl x => rfl
      | inr z =>
        obtain ⟨s, p⟩ := z
        induction p using Quot.inductionOn with
        | h z => cases z with
          | inl z => cases z <;> rfl
          | inr z => rfl

/-- The actual corner maps preserve the identity cube strictly. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchangeNaturality.lean:98"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision", simp]
theorem coneSquareMap_id (a : S ⟶ T) :
    coneSquareMap (𝟙 (Arrow.mk a)) = 𝟙 (coneSquare a) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext <;> apply Hom.ext <;> funext n <;>
    apply ReducedMappingCone.hom_ext <;> intro z <;> rfl

/-- The actual corner maps preserve the composite of original cubes strictly. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchangeNaturality.lean:104"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision", simp]
theorem coneSquareMap_comp {S'' T'' : Arrow (Arrow LoopPrespectrum.{u})}
    {c : S'' ⟶ T''} (l : Arrow.mk b ⟶ Arrow.mk c) :
    coneSquareMap (k ≫ l) = coneSquareMap k ≫ coneSquareMap l := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext <;> apply Hom.ext <;> funext n <;>
    apply ReducedMappingCone.hom_ext <;> intro z <;> rfl

/-- Pointwise original cofibers form a functor on the actual strict cubes. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchangeNaturality.lean:111"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
def coneSquareFunctor :
    Arrow (Arrow (Arrow LoopPrespectrum.{u})) ⥤ Arrow (Arrow LoopPrespectrum.{u}) where
  obj X := coneSquare X.hom
  map k := coneSquareMap k
  map_id X := coneSquareMap_id X.hom
  map_comp k l := coneSquareMap_comp k l

end Topology.LoopPrespectrum.StrictSquare

