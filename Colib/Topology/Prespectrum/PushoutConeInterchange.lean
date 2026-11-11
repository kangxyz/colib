/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeMapHomotopy
public import Colib.Topology.Prespectrum.PushoutMovingHomotopy
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Original cones commute with reduced two-leg pushouts

For an actual span of strict arrow squares, the cone of the unchanged reduced-pushout map
is isomorphic to the reduced pushout of the three original cones. Both interval coordinates
and the structure-loop parameter remain independent. Whole interval-valued families descend
before evaluation, so no product-preservation property of arbitrary quotient maps is assumed.
The comparison uses no separation, point HEP, or stable excision hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : Arrow LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The actual original map between the two rows of the span of arrows. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:32"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def spanArrowMap : prespectrum f.left g.left ⟶ prespectrum f.right g.right :=
  map f.left g.left f.right g.right A.hom B.hom C.hom f.w g.w

/-- The original target row maps into the pushout of the three literal cone inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:36"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeTarget : prespectrum f.right g.right ⟶
    prespectrum (mappingConeMap f) (mappingConeMap g) :=
  map f.right g.right (mappingConeMap f) (mappingConeMap g)
    (mappingConeInclusion A.hom) (mappingConeInclusion B.hom) (mappingConeInclusion C.hom)
    (by apply Hom.ext; funext n; ext x; rfl)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- The original left cone cylinder, included in the unchanged cone span. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:44"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeLeftNull :
    Homotopy (B.hom ≫ mappingConeInclusion B.hom ≫ inl (mappingConeMap f) (mappingConeMap g))
      (zeroHom B.left (prespectrum (mappingConeMap f) (mappingConeMap g))) :=
  ((mappingConeHomotopy B.hom).postcomp (inl (mappingConeMap f) (mappingConeMap g))).cast
    (by rfl) (by apply Hom.ext; funext n; ext x; rfl)

/-- The original right cone cylinder, included in the same unchanged cone span. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:51"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeRightNull :
    Homotopy (C.hom ≫ mappingConeInclusion C.hom ≫ inr (mappingConeMap f) (mappingConeMap g))
      (zeroHom C.left (prespectrum (mappingConeMap f) (mappingConeMap g))) :=
  ((mappingConeHomotopy C.hom).postcomp (inr (mappingConeMap f) (mappingConeMap g))).cast
    (by rfl) (by
      apply Hom.ext
      funext n
      ext x
      exact (inr (mappingConeMap f) (mappingConeMap g)).map_point n)

/-- The actual overlap track after the original row map and cone inclusion map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:62"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeInitialTrack :
    Homotopy
      (f.left ≫ B.hom ≫ mappingConeInclusion B.hom ≫ inl (mappingConeMap f) (mappingConeMap g))
      (g.left ≫ C.hom ≫ mappingConeInclusion C.hom ≫ inr (mappingConeMap f) (mappingConeMap g)) :=
  ((glue f.left g.left).postcomp (spanArrowMap f g ≫ coneInterchangeTarget f g)).cast
    (by apply Hom.ext; funext n; ext x; rfl)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- The endpoint of the contraction is the literal constant zero overlap track. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:71"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeFinalTrack :
    Homotopy
      (f.left ≫ zeroHom B.left (prespectrum (mappingConeMap f) (mappingConeMap g)))
      (g.left ≫ zeroHom C.left (prespectrum (mappingConeMap f) (mappingConeMap g))) :=
  (Homotopy.refl (zeroHom A.left (prespectrum (mappingConeMap f) (mappingConeMap g)))).cast rfl rfl

/-- Two original cylinder parameters supply the complete moving square, including its four faces. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:78"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeSquare :
    (coneInterchangeInitialTrack f g).Square (coneInterchangeFinalTrack f g)
      (Homotopy.precomp f.left (coneInterchangeLeftNull f g))
      (Homotopy.precomp g.left (coneInterchangeRightNull f g)) where
  level n := ⟨fun z ↦ cylinder (mappingConeMap f) (mappingConeMap g) n
    (z.2.1, ReducedMappingCone.cylinder (A.left.point n) (A.right.point n) (A.hom.map n)
      (z.1, z.2.2)), by fun_prop⟩
  at_zero n s x := by
    change cylinder (mappingConeMap f) (mappingConeMap g) n
      (s, ReducedMappingCone.cylinder _ _ _ (0, x)) = _
    rw [ReducedMappingCone.cylinder_zero]
    rfl
  at_one n s x := by
    change cylinder (mappingConeMap f) (mappingConeMap g) n
      (s, ReducedMappingCone.cylinder _ _ _ (1, x)) = _
    rw [ReducedMappingCone.cylinder_one]
    exact cylinder_point (mappingConeMap f) (mappingConeMap g) n s
  left n r x := by
    change cylinder (mappingConeMap f) (mappingConeMap g) n
      (0, ReducedMappingCone.cylinder _ _ _ (r, x)) = _
    rw [cylinder_zero]
    rfl
  right n r x := by
    change cylinder (mappingConeMap f) (mappingConeMap g) n
      (1, ReducedMappingCone.cylinder _ _ _ (r, x)) = _
    rw [cylinder_one]
    rfl
  at_point n r s := by
    change cylinder (mappingConeMap f) (mappingConeMap g) n
      (s, ReducedMappingCone.cylinder _ _ _ (r, A.left.point n)) = _
    rw [ReducedMappingCone.cylinder_base]
    exact cylinder_point (mappingConeMap f) (mappingConeMap g) n s
  comm _n _r _s _x _t := rfl

/-- Descend the actual two-cylinder square before evaluating the cone-contraction parameter. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:113"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeNull :
    Homotopy (spanArrowMap f g ≫ coneInterchangeTarget f g)
      (zeroHom (prespectrum f.left g.left)
        (prespectrum (mappingConeMap f) (mappingConeMap g))) :=
  (descSquareHomotopy f.left g.left (coneInterchangeLeftNull f g)
    (coneInterchangeRightNull f g) (coneInterchangeSquare f g)).cast
    (by
      apply hom_ext
      · apply Hom.ext; funext n; ext x; rfl
      · apply Hom.ext; funext n; ext x; rfl
      · intro n s x; rfl)
    (by
      apply hom_ext
      · apply Hom.ext; funext n; ext x; rfl
      · apply Hom.ext; funext n; ext x; rfl
      · intro n s x; rfl)

/-- The unchanged cone of the row map descends to the pushout of the original cones. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:131"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchange : mappingCone (spanArrowMap f g) ⟶
    prespectrum (mappingConeMap f) (mappingConeMap g) :=
  mappingConeDesc (spanArrowMap f g) (coneInterchangeTarget f g) (coneInterchangeNull f g)

/-- The original left row inclusions form the strict square into the actual row map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:136"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeLeftSquare : B ⟶ Arrow.mk (spanArrowMap f g) :=
  Arrow.homMk (inl f.left g.left) (inl f.right g.right)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- The original right row inclusions form the strict square into the same actual row map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:141"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeRightSquare : C ⟶ Arrow.mk (spanArrowMap f g) :=
  Arrow.homMk (inr f.left g.left) (inr f.right g.right)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- Original row-cylinder homotopies induce the full reverse overlap track on the original cone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:146"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeInvTrack :
    Homotopy (mappingConeMap f ≫ mappingConeMap (coneInterchangeLeftSquare f g))
      (mappingConeMap g ≫ mappingConeMap (coneInterchangeRightSquare f g)) :=
  (mappingConeMapHomotopy
    (s := f ≫ coneInterchangeLeftSquare f g)
    (t := g ≫ coneInterchangeRightSquare f g)
    (glue f.left g.left) (glue f.right g.right) (by intros; rfl)).cast
    (mappingConeFunctor.map_comp f (coneInterchangeLeftSquare f g))
    (mappingConeFunctor.map_comp g (coneInterchangeRightSquare f g))

/-- The actual cone maps and original cylinder track reassemble the unchanged row-map cone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:157"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeInv : prespectrum (mappingConeMap f) (mappingConeMap g) ⟶
    mappingCone (spanArrowMap f g) :=
  desc (mappingConeMap f) (mappingConeMap g)
    (mappingConeMap (coneInterchangeLeftSquare f g))
    (mappingConeMap (coneInterchangeRightSquare f g)) (coneInterchangeInvTrack f g)

/-- The two actual quotient descents are inverse on the original row-map cone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:164"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
theorem coneInterchange_hom_inv :
    coneInterchange f g ≫ coneInterchangeInv f g = 𝟙 (mappingCone (spanArrowMap f g)) := by
  apply mappingCone_hom_ext
  · apply hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n r q
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z <;> rfl
      | inr z => rfl

/-- The same quotient descents are inverse on the unchanged pushout of the original cones. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:178"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
theorem coneInterchange_inv_hom :
    coneInterchangeInv f g ≫ coneInterchange f g =
      𝟙 (prespectrum (mappingConeMap f) (mappingConeMap g)) := by
  apply hom_ext
  · apply mappingCone_hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · apply mappingCone_hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n s q
    induction q using Quot.inductionOn with
    | h z => cases z <;> rfl

/-- Literal interchange of the original reduced pushout and original reduced mapping cone. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:193"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
def coneInterchangeIso : mappingCone (spanArrowMap f g) ≅
    prespectrum (mappingConeMap f) (mappingConeMap g) where
  hom := coneInterchange f g
  inv := coneInterchangeInv f g
  hom_inv_id := coneInterchange_hom_inv f g
  inv_hom_id := coneInterchange_inv_hom f g

/-- The forward comparison preserves the original target row and its entire overlap cylinder. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:201"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
theorem coneInterchange_inclusion :
    mappingConeInclusion (spanArrowMap f g) ≫ coneInterchange f g = coneInterchangeTarget f g :=
  mappingConeInclusion_desc _ _ _

/-- The independent outer cone and inner span times remain in that order. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeInterchange.lean:206"
  "adaptation" "Original actual cone/pushout interchange retaining whole interval families."]
theorem coneInterchange_doubleCylinder (n : ℕ) (r s : unitInterval) (x : A.left.space n) :
    (coneInterchange f g).map n
      (ReducedMappingCone.cylinder ((prespectrum f.left g.left).point n)
        ((prespectrum f.right g.right).point n) ((spanArrowMap f g).map n)
        (r, cylinder f.left g.left n (s, x))) =
      cylinder (mappingConeMap f) (mappingConeMap g) n
        (s, ReducedMappingCone.cylinder (A.left.point n) (A.right.point n) (A.hom.map n)
          (r, x)) := rfl

end Topology.LoopPrespectrum.HomotopyPushout
