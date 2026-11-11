/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.PushoutConeRebracketing
public import Colib.Topology.Prespectrum.PushoutPointCone
public import Colib.Topology.Prespectrum.PushoutWeakEquivalence
public import Colib.Topology.Prespectrum.ConeContraction
public import Colib.Topology.Prespectrum.PointHEP
public import Colib.Topology.HomotopyCofiber.ReducedMappingConeCollapse

/-!
# Genuine collapse of the original right-inclusion cone

The actual map cone(C→HPO(f,g))→cone(f) keeps B and the full A-cylinder, and collapses the
attached C-cone. Literal quotient rebracketing factors it through the actual contraction of
cone(id_C). Original complete-weak pushout preservation therefore proves this exact map weak
under HEP of the three original points, with no stable-excision assumption.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- Collapse the original right endpoint, keeping B and every value of the original A-cylinder. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:33"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
def collapseRight : prespectrum f g ⟶ mappingCone f :=
  desc f g (mappingConeInclusion f) (zeroHom C (mappingCone f))
    ((mappingConeHomotopy f).cast rfl rfl)

/-- The original C inclusion becomes literally constant after the displayed collapse. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:38"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
def collapseRightNull : Homotopy (inr f g ≫ collapseRight f g) (zeroHom C (mappingCone f)) :=
  (Homotopy.refl (zeroHom C (mappingCone f))).cast rfl rfl

/-- The actual original cone collapse, with its newly attached C-cylinder sent to the point. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:42"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
def rightConeCollapse : mappingCone (inr f g) ⟶ mappingCone f :=
  mappingConeDesc (inr f g) (collapseRight f g) (collapseRightNull f g)

/-- The actual collapse preserves the original B inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:46"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision.",
  simp]
theorem rightConeCollapse_left (n : ℕ) (y : B.space n) :
    (rightConeCollapse f g).map n ((mappingConeInclusion (inr f g)).map n ((inl f g).map n y)) =
      (mappingConeInclusion f).map n y := rfl

/-- The original overlap cylinder is unchanged under collapse. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:51"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision.",
  simp]
theorem rightConeCollapse_overlap (n : ℕ) (s : unitInterval) (x : A.space n) :
    (rightConeCollapse f g).map n ((mappingConeInclusion (inr f g)).map n
      (cylinder f g n (s, x))) =
        ReducedMappingCone.cylinder (A.point n) (B.point n) (f.map n) (s, x) := rfl

/-- Every value of the newly attached original C-cylinder maps to the literal cone point. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:57"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision.",
  simp]
theorem rightConeCollapse_attachedCylinder (n : ℕ) (s : unitInterval) (x : C.space n) :
    (rightConeCollapse f g).map n
      (ReducedMappingCone.cylinder (C.point n) ((prespectrum f g).point n)
        ((inr f g).map n) (s, x)) = (mappingCone f).point n := rfl

/-- The original identity-cone collapse gives the middle strict map in the actual factorization. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:63"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
def rightConePointMap : prespectrum f (g ≫ mappingConeInclusion (𝟙 C)) ⟶
    prespectrum f (zeroHom A pointPrespectrum) :=
  map f (g ≫ mappingConeInclusion (𝟙 C)) f (zeroHom A pointPrespectrum)
    (𝟙 A) (𝟙 B) (zeroHom (mappingCone (𝟙 C)) pointPrespectrum) (by simp)
    (by apply Hom.ext; funext n; ext x; rfl)

/-- Original collapse is exactly rebracketing, identity-cone collapse and point removal. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:70"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
theorem rightConeCollapse_factor :
    rightConeCollapse f g = rightConeRebracket f g ≫ rightConePointMap f g ≫ pointConeMap f := by
  apply mappingCone_hom_ext
  · apply hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n s x; rfl

private def levelHomeomorph {E F : LoopPrespectrum.{u}} (e : E ≅ F) (n : ℕ) :
    E.space n ≃ₜ F.space n where
  toFun := e.hom.map n
  invFun := e.inv.map n
  left_inv x := congrArg (fun h ↦ h.map n x) e.hom_inv_id
  right_inv x := congrArg (fun h ↦ h.map n x) e.inv_hom_id
  continuous_toFun := (e.hom.map n).continuous
  continuous_invFun := (e.inv.map n).continuous

/-- The original identity-cone contraction gives its actual map to the literal point equivalence. -/
private def identityConePointEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ((mappingCone (𝟙 C)).space n) (pointPrespectrum.{u}.space n) where
  toFun := (zeroHom (mappingCone (𝟙 C)) pointPrespectrum).map n
  invFun := ContinuousMap.const _ ((mappingCone (𝟙 C)).point n)
  left_inv := ⟨((mappingConeIdContraction C).levelHomotopy n).symm.toHomotopy⟩
  right_inv := by
    have he : ((zeroHom (mappingCone (𝟙 C)) pointPrespectrum).map n).comp
        (ContinuousMap.const (pointPrespectrum.{u}.space n) ((mappingCone (𝟙 C)).point n)) =
          ContinuousMap.id _ := by
      ext x
      change (PUnit.unit : PUnit.{u + 1}) = x
      exact Subsingleton.elim _ _
    rw [he]

/-- Under original point HEP, the exact original C-cone collapse is a complete weak equivalence. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutConeCollapse.lean:104"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
theorem rightConeCollapse_level_isWeakHomotopyEquivalence (n : ℕ)
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point n))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point n))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point n)))) :
    IsWeakHomotopyEquivalence ((rightConeCollapse f g).map n) := by
  have hcone : TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{u + 1} ((mappingCone (𝟙 C)).point n))) :=
    ReducedMappingCone.point_homotopyExtensionProperty
      (C.point n) (C.point n) ((𝟙 C : C ⟶ C).map n) rfl hC hC
  have hmid : IsWeakHomotopyEquivalence ((rightConePointMap f g).map n) :=
    map_level_isWeakHomotopyEquivalence f (g ≫ mappingConeInclusion (𝟙 C))
      f (zeroHom A pointPrespectrum) (𝟙 A) (𝟙 B)
      (zeroHom (mappingCone (𝟙 C)) pointPrespectrum) (by simp)
      (by apply Hom.ext; funext k; ext x; rfl) n hA hB hcone hA hB
      (pointPrespectrum_point_homotopyExtensionProperty n)
      (isWeakHomotopyEquivalence_id (A.space n)) (isWeakHomotopyEquivalence_id (B.space n))
      (isWeakHomotopyEquivalence_of_homotopyEquiv (identityConePointEquiv (C := C) n))
  rw [rightConeCollapse_factor]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv
    (levelHomeomorph (pointConeIso f) n).toHomotopyEquiv).comp
      (hmid.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
        (levelHomeomorph (rightConeRebracketIso f g) n).toHomotopyEquiv))

end Topology.LoopPrespectrum.HomotopyPushout
