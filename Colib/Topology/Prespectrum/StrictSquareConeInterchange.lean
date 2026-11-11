/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeConeTranspose
public import Colib.Topology.Prespectrum.PushoutConeInterchange
public import Colib.Topology.Prespectrum.StrictSquareCone

/-!
# The original strict-square cone commutes with pointwise cofibers

A morphism of strict squares gives four actual corner cones. Their original strict cone maps
form a square. The cone of the unlooped Bass map is isomorphic to the unlooped Bass value of
that square. This factors the literal double-cone transpose and cone/pushout interchange;
its comparison equation is checked on every original quotient stratum. No topology or stable
excision hypothesis enters the point-set isomorphism. The double-cone coordinate swap remains
explicit, and no equality of orientation-sensitive iterated boundaries is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)

/-- The original top face, viewed as a square between the two actual corner arrows. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:33"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
def coneTopFace : Arrow.mk a.left.left ⟶ Arrow.mk a.left.right :=
  Arrow.homMk S.left.hom T.left.hom a.left.w.symm

/-- The original bottom face between the two actual bottom corner arrows. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:37"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
def coneBottomFace : Arrow.mk a.right.left ⟶ Arrow.mk a.right.right :=
  Arrow.homMk S.right.hom T.right.hom a.right.w.symm

/-- The original left face retains the given square-map equation. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:41"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
def coneLeftFace : Arrow.mk a.left.left ⟶ Arrow.mk a.right.left :=
  Arrow.homMk S.hom.left T.hom.left (congrArg (fun f ↦ f.left) a.w).symm

/-- The original right face retains the other component of the given square-map equation. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:45"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
def coneRightFace : Arrow.mk a.left.right ⟶ Arrow.mk a.right.right :=
  Arrow.homMk S.hom.right T.hom.right (congrArg (fun f ↦ f.right) a.w).symm

/-- The four original corner cones and their original strict maps form a commuting square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:49"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
def coneSquare : Arrow (Arrow LoopPrespectrum.{u}) :=
  Arrow.mk (Arrow.homMk
    (f := Arrow.mk (mappingConeMap (coneTopFace a)))
    (g := Arrow.mk (mappingConeMap (coneBottomFace a)))
    (mappingConeMap (coneLeftFace a)) (mappingConeMap (coneRightFace a)) (by
      change mappingConeFunctor.map (coneLeftFace a) ≫
          mappingConeFunctor.map (coneBottomFace a) =
        mappingConeFunctor.map (coneTopFace a) ≫ mappingConeFunctor.map (coneRightFace a)
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply Arrow.hom_ext
      · exact S.hom.w
      · exact T.hom.w))

/-- The literal cone of the unchanged span map is the span of the three original corner cones. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:64"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
def coneSpanIso : mappingCone (spanMap a) ≅ span (coneSquare a) :=
  HomotopyPushout.coneInterchangeIso (coneTopFace a) (coneLeftFace a)

/-- The finite span interchange retains the original constant-track comparison map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:68"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
theorem coneSpanIso_comparison :
    (coneSpanIso a).hom ≫ comparison (coneSquare a) =
      ConeConeTranspose.vertical (comparison S) (comparison T) (spanMap a) a.right.right
        (comparison_naturality a) := by
  apply mappingCone_hom_ext
  · apply HomotopyPushout.hom_ext
    · apply Hom.ext; funext n; ext x; rfl
    · apply Hom.ext; funext n; ext x; rfl
    · intro n s x; rfl
  · intro n r q
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z <;> rfl
      | inr z => rfl

/-- The transpose target is isomorphic to the original comparison arrow of the cone square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:84"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
def coneComparisonIso :
    Arrow.mk (ConeConeTranspose.vertical (comparison S) (comparison T) (spanMap a)
      a.right.right (comparison_naturality a)) ≅
        Arrow.mk (comparison (coneSquare a)) :=
  Arrow.isoMk (f := Arrow.mk (ConeConeTranspose.vertical (comparison S) (comparison T)
      (spanMap a) a.right.right (comparison_naturality a)))
    (g := Arrow.mk (comparison (coneSquare a)))
    (coneSpanIso a) (Iso.refl (mappingCone a.right.right)) (by
      change (coneSpanIso a).hom ≫ comparison (coneSquare a) =
        ConeConeTranspose.vertical (comparison S) (comparison T) (spanMap a) a.right.right
          (comparison_naturality a) ≫ 𝟙 _
      rw [Category.comp_id]
      exact coneSpanIso_comparison a)

/-- Original unlooped square cones commute with the actual four-corner cofiber square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:99"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
def coneInterchangeIso :
    mappingCone (mappingConeMap (strictSquareComparisonFunctor.map a)) ≅
      mappingCone (comparison (coneSquare a)) :=
  ConeConeTranspose.iso (comparison S) (comparison T) (spanMap a) a.right.right
    (comparison_naturality a) ≪≫ mappingConeFunctor.mapIso (coneComparisonIso a)

/-- The original double target is retained by the actual strict-square interchange. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:106"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
theorem coneInterchangeIso_inclusion_inclusion (n : ℕ) (y : T.right.right.space n) :
    (coneInterchangeIso a).hom.map n
      ((mappingConeInclusion (mappingConeMap (strictSquareComparisonFunctor.map a))).map n
        ((mappingConeInclusion (comparison T)).map n y)) =
      (mappingConeInclusion (comparison (coneSquare a))).map n
        ((mappingConeInclusion a.right.right).map n y) := rfl

/-- On the original double cylinder the two cone times are swapped before span interchange. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareConeInterchange.lean:114"
  "adaptation" "Original actual four-corner cone square and double-cone interchange."]
theorem coneInterchangeIso_doubleCylinder (n : ℕ) (r s : unitInterval)
    (x : (span S).space n) :
    (coneInterchangeIso a).hom.map n
      (ReducedMappingCone.cylinder ((mappingCone (comparison S)).point n)
        ((mappingCone (comparison T)).point n)
        ((mappingConeMap (strictSquareComparisonFunctor.map a)).map n)
        (r, ReducedMappingCone.cylinder ((span S).point n) (S.right.right.point n)
          ((comparison S).map n) (s, x))) =
      ReducedMappingCone.cylinder ((span (coneSquare a)).point n)
        ((mappingCone a.right.right).point n) ((comparison (coneSquare a)).map n)
        (s, (coneSpanIso a).hom.map n
          (ReducedMappingCone.cylinder ((span S).point n) ((span T).point n)
            ((spanMap a).map n) (r, x))) := rfl

end Topology.LoopPrespectrum.StrictSquare

namespace Topology.LoopPrespectrum.StrictSquare

attribute [colib_tag "COL-0571"] coneInterchangeIso

end Topology.LoopPrespectrum.StrictSquare
