/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Smooth.CodimensionOneDominance
public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk

/-!
# Codimension of closed points in a generic smooth fibre

Over a generic point of a reduced base, the original source stalk is canonically
its actual fibre stalk: the extended maximal ideal of the base stalk vanishes.
Thus a point closed in a smooth fibre of relative dimension `n` has coheight `n`
in the original source. A finite closed support supplies the finite residue
extension needed for closedness, without requiring that support to be flat.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Order

universe u

namespace AlgebraicGeometry.Scheme

/-- The extended maximal ideal vanishes over a generic point of a reduced base. -/
theorem map_maximalIdeal_eq_bot_of_image_mem_genericPoints
    {X S : Scheme.{u}} (q : X ⟶ S) [IsReduced S]
    (x : X) (hx : q x ∈ genericPoints S) :
    Ideal.map (q.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (q x))) = ⊥ := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp
    (isField_stalk_of_closure_mem_irreducibleComponents S (q x) hx)]
  exact Ideal.map_bot

/-- The original stalk equals the stalk of the actual fibre over a generic point
of a reduced base, via the native quotient-to-fibre equivalence. -/
@[colib_tag "COL-1090",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibreStalk.lean:343-369"
    "specialization" "The canonical fibre stalk quotient over a generic point of a reduced base"]
def stalkEquivFiberStalkOfGeneric
    {X S : Scheme.{u}} (q : X ⟶ S) [IsReduced S]
    (x : X) (hx : q x ∈ genericPoints S) :
    X.presheaf.stalk x ≃+* (q.fiber (q x)).presheaf.stalk (q.asFiber x) :=
  (RingEquiv.quotientBot (X.presheaf.stalk x)).symm.trans
    ((Ideal.quotientEquivAlgOfEq (X.presheaf.stalk x)
      (map_maximalIdeal_eq_bot_of_image_mem_genericPoints q x hx).symm).toRingEquiv.trans
        (quotientStalkEquivFiberStalk q x))

/-- This equivalence is the actual fibre-inclusion stalk map, with its canonical
point identification, rather than an unspecified abstract ring equivalence. -/
theorem stalkEquivFiberStalkOfGeneric_apply
    {X S : Scheme.{u}} (q : X ⟶ S) [IsReduced S]
    (x : X) (hx : q x ∈ genericPoints S) (b : X.presheaf.stalk x) :
    stalkEquivFiberStalkOfGeneric q x hx b =
      ((q.fiberι (q x)).stalkMap (q.asFiber x)).hom
        ((X.presheaf.stalkCongr (.of_eq (q.fiberι_asFiber x).symm)).hom b) := by
  exact quotientStalkEquivFiberStalk_mk q x b

/-- A point closed in its smooth fibre over a generic point of a reduced base
has coheight equal to the relative dimension in the original source scheme. -/
@[colib_tag "COL-1090",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Picard/SmoothCurveLocalDimension.lean:114-117,254-257"
    "adaptation" "Closed smooth-fibre dimension transported to the original source stalk"]
theorem coheight_eq_of_image_mem_genericPoints_closed_fiber
    {X S : Scheme.{u}} (q : X ⟶ S) [IsReduced S] (n : ℕ)
    [SmoothOfRelativeDimension n q] (x : X) (hx : q x ∈ genericPoints S)
    (hc : IsClosed ({q.asFiber x} : Set (q.fiber (q x)))) :
    coheight x = n := by
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : Smooth (q.fiberToSpecResidueField (q x)) := by
    change Smooth (CategoryTheory.Limits.pullback.snd q (S.fromSpecResidueField (q x)))
    infer_instance
  have : LocallyOfFiniteType (q.fiberToSpecResidueField (q x)) := inferInstance
  have hd : ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞) :=
    (stalkEquivFiberStalkOfGeneric q x hx).ringKrullDim.trans
      ((topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point
        (k := S.residueField (q x)) (q.fiberToSpecResidueField (q x)) (q.asFiber x) hc).symm.trans
          (fiberDimensionAt_eq_of_smoothOfRelativeDimension q n x))
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd

/-- A finite residue extension over a generic base point gives the original
source codimension, not merely the codimension of an image support. -/
theorem coheight_eq_of_image_mem_genericPoints_finite_residue
    {X S : Scheme.{u}} (q : X ⟶ S) [IsReduced S] (n : ℕ)
    [SmoothOfRelativeDimension n q] [IsSeparated q]
    (x : X) (hx : q x ∈ genericPoints S) (hf : (q.residueFieldMap x).hom.Finite) :
    coheight x = n :=
  coheight_eq_of_image_mem_genericPoints_closed_fiber q n x hx
    (isClosed_asFiber_of_finite_residueFieldMap q x hf)

/-- A whole finite closed support supplies the residue finiteness internally.
The resulting codimension is that of its point in the original smooth source. -/
@[colib_tag "COL-1090"]
theorem coheight_eq_of_image_mem_genericPoints_finite_closed_support
    {D X S : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (q : X ⟶ S) [IsReduced S] (n : ℕ)
    [SmoothOfRelativeDimension n q] [IsSeparated q] [IsFinite (i ≫ q)]
    (x : D) (hx : q (i x) ∈ genericPoints S) : coheight (i x) = n :=
  coheight_eq_of_image_mem_genericPoints_finite_residue q n (i x) hx
    (residueFieldMap_finite_of_finite_closed_support i q x)

/-- On a finite closed support of a smooth relative curve over a reduced base,
original-source codimension one is equivalent to genericity of the base image. -/
@[colib_tag "COL-1090"]
theorem coheight_eq_one_iff_image_mem_genericPoints_of_finite_closed_support
    {D X S : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (q : X ⟶ S) [IsReduced S] [SmoothOfRelativeDimension 1 q] [IsSeparated q]
    [IsFinite (i ≫ q)] (x : D) :
    coheight (i x) = 1 ↔ q (i x) ∈ genericPoints S :=
  ⟨image_mem_genericPoints_of_coheight_one_finite_closed_support i q x,
    coheight_eq_of_image_mem_genericPoints_finite_closed_support i q 1 x⟩

end AlgebraicGeometry.Scheme
