/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterStalkMaps
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence

/-!
# One ordered parameter-diagonal family in the original ambient and coefficient stalks

At an actual coefficient parameter-quotient point, choose one regular list in
the parameter-diagonal stalk ideal. The ambient list is its image under the
actual ambient parameter stalk map. The coefficient list is the image of
that ambient list under the actual support-inclusion stalk map.

Flatness of the two maps to `T ×[k] T` transports weak regularity by the
public Stacks theorem `isWeaklyRegular_map_of_flat`. The two exact kernel
identities from `ParameterStalkMaps` make the generated ideals proper, so
both lists are regular. The support inclusion itself need not be flat.
There is only one choice of a list; no independent target choice, permutation,
Tor hypothesis, or regularity of the remaining middle equations is used.

All schemes and local rings are the native ones, including the full possibly
nonreduced quotient. Empty or disconnected original smooth schemes are allowed.
Geometric integrality of `T` is used only by the native exterior-support input.

## Exact source providers

At AxiomMath/Stacks commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`:
* `StacksFrontier/AlgebraicGeometry/Divisors/Relative/SmoothSection.lean:65-71`,
  `isRegularImmersion_of_smooth_section` (native Tag 067R);
* `StacksFrontier/AlgebraicGeometry/MoreMorphisms/RegularImmersion/PerfectFactor.lean:307-317`,
  regular generators of the actual immersion stalk kernel;
* `RegularOpenIndependence.lean:60-71` in the same regular-immersion directory,
  public ordered-list flat transport, used twice.

At Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`:
* `Mathlib/RingTheory/Regular/RegularSequence.lean:60-63,719-724`,
  images of list ideals and proper weakly regular lists in a local ring;
* `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:100-102`, actual flat stalk maps.

The construction is an application of these ingredients, not an attribution
of the full common-list statement to a single Stacks tag. The companion
report proposes a version-exact software bibliography record; no mismatched
existing `axiom_stacks` entry is used here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (Z : SmoothSite (Spec (.of k)))
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "A" => correspondenceIntersectionAmbient
  (SmoothSite.product X T).hom (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct
  (SmoothSite.product X T).hom (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
  (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "j" =>
  nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "i" => correspondenceSupportProductInclusion
  (SmoothSite.product X T).hom (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
  (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
local notation3 (prettyPrint := false) "a" => exteriorAmbientParameterPair X Y Z T
local notation3 (prettyPrint := false) "p" =>
  nativeExteriorCoefficientParameterPair X Y T z hz Z w hw

/-- One base list, with its two ordered images in the original ambient and coefficient stalks.
The kernel equations refer to the actual quotient maps, not arbitrary isomorphic quotients. -/
structure NativeExteriorParameterStalkFamily (x : Q) where
  /-- The sole chosen list, in the actual parameter-diagonal base stalk. -/
  baseList : List ((pullback T.hom T.hom).presheaf.stalk (a (i (j x))))
  /-- Regularity comes from the smooth parameter diagonal. -/
  base_regular : IsRegular ((pullback T.hom T.hom).presheaf.stalk (a (i (j x)))) baseList
  /-- Exact generation of the full base diagonal ideal. -/
  base_ideal : Ideal.ofList baseList =
    IdealSheafData.stalk (pullback.diagonal T.hom).ker (a (i (j x)))
  /-- The ambient family is the literal ordered image of `baseList`. -/
  ambient_regular : IsRegular ((A).presheaf.stalk (i (j x)))
    (baseList.map ((a).stalkMap (i (j x))).hom)
  /-- The original ambient parameter quotient has exactly this kernel. -/
  ambient_kernel :
    RingHom.ker (nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw x).hom =
      Ideal.ofList (baseList.map ((a).stalkMap (i (j x))).hom)
  /-- The coefficient family is the image of the ambient family through the support inclusion. -/
  coefficient_regular : IsRegular ((P).presheaf.stalk (j x))
    ((baseList.map ((a).stalkMap (i (j x))).hom).map ((i).stalkMap (j x)).hom)
  /-- The actual coefficient parameter quotient has exactly the mapped ambient kernel. -/
  coefficient_kernel : RingHom.ker ((j).stalkMap x).hom =
    Ideal.ofList ((baseList.map ((a).stalkMap (i (j x))).hom).map ((i).stalkMap (j x)).hom)

/-- Construct the single family from the parameter diagonal, then transport it twice.
Properness is proved using the literal quotient kernels at `x`, never assumed. -/
def nativeExteriorParameterStalkFamily (x : Q) :
    NativeExteriorParameterStalkFamily X Y T z hz Z w hw x := by
  classical
  let δ := pullback.diagonal T.hom
  let t := pullback.fst δ p x
  have ht : a (i (j x)) = δ t := by
    calc
      a (i (j x)) = p (j x) := nativeExteriorParameter_basePoint X Y T z hz Z w hw x
      _ = δ t :=
        (congrArg (fun f : Q ⟶ pullback T.hom T.hom => f x)
          (pullback.condition (f := δ) (g := p))).symm
  have hex : ∃ l : List ((pullback T.hom T.hom).presheaf.stalk (a (i (j x)))),
      IsRegular ((pullback T.hom T.hom).presheaf.stalk (a (i (j x)))) l ∧
        Ideal.ofList l = IdealSheafData.stalk δ.ker (a (i (j x))) := by
    rw [ht]
    obtain ⟨l, hl, hk⟩ :=
      Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
        δ (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
          (pullback.fst T.hom T.hom) δ (pullback.diagonal_fst T.hom)) t
    exact ⟨l, hl, hk.trans (ker_stalkMap_eq_idealStalk_ker δ t)⟩
  let l := Classical.choose hex
  have hl := (Classical.choose_spec hex).1
  have hk := (Classical.choose_spec hex).2
  have hA : IsWeaklyRegular ((A).presheaf.stalk (i (j x)))
      (l.map ((a).stalkMap (i (j x))).hom) :=
    Stacks.AlgebraicGeometry.isWeaklyRegular_map_of_flat
      ((a).stalkMap (i (j x))).hom (Flat.stalkMap a _) hl.toIsWeaklyRegular
  have hAk :
      RingHom.ker (nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw x).hom =
        Ideal.ofList (l.map ((a).stalkMap (i (j x))).hom) := by
    rw [nativeExteriorAmbientParameterStalkMap_ker, ← hk, Ideal.map_ofList]
  haveI : Flat (i ≫ a) := nativeExteriorParameter_composite_flat X Y T z hz Z w hw
  have hC : IsWeaklyRegular ((P).presheaf.stalk (j x))
      ((l.map ((a).stalkMap (i (j x))).hom).map ((i).stalkMap (j x)).hom) := by
    have hflat : IsWeaklyRegular ((P).presheaf.stalk (j x))
        (l.map ((i ≫ a).stalkMap (j x)).hom) :=
      Stacks.AlgebraicGeometry.isWeaklyRegular_map_of_flat
        ((i ≫ a).stalkMap (j x)).hom (Flat.stalkMap (i ≫ a) _)
        (l := l) hl.toIsWeaklyRegular
    have hlist :
        (l.map ((a).stalkMap (i (j x))).hom).map ((i).stalkMap (j x)).hom =
          l.map ((i ≫ a).stalkMap (j x)).hom := by
      rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, RingHom.coe_comp, List.map_map]
      rfl
    rw [hlist]
    exact hflat
  have hCk : RingHom.ker ((j).stalkMap x).hom =
      Ideal.ofList ((l.map ((a).stalkMap (i (j x))).hom).map ((i).stalkMap (j x)).hom) := by
    rw [nativeExteriorParameterDiagonal_stalkMap_ker_composite, ← hk,
      Ideal.map_ofList, Ideal.map_ofList]
  refine ⟨l, hl, hk, ?_, hAk, ?_, hCk⟩
  · refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ (fun r hr => ?_) hA
    apply IsLocalRing.le_maximalIdeal
      (RingHom.ker_ne_top (nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw x).hom)
    rw [hAk]
    exact Ideal.subset_span hr
  · refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ (fun r hr => ?_) hC
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ((j).stalkMap x).hom)
    rw [hCk]
    exact Ideal.subset_span hr

namespace NativeExteriorParameterStalkFamily

variable {X Y T z hz Z w hw}
  {x : nativeExteriorParameterDiagonal X Y T z hz Z w hw}
  (F : NativeExteriorParameterStalkFamily X Y T z hz Z w hw x)

/-- The ordered ambient family, with precisely the original ambient scalar map. -/
abbrev ambientList : List ((A).presheaf.stalk (i (j x))) :=
  F.baseList.map ((a).stalkMap (i (j x))).hom

/-- The ordered coefficient family, using precisely the actual support-inclusion scalar map. -/
abbrev coefficientList : List ((P).presheaf.stalk (j x)) :=
  F.ambientList.map ((i).stalkMap (j x)).hom

/-- The same coefficient list is obtained by the actual parameter map and its true point cast. -/
theorem coefficientList_eq_parameter_image :
    F.coefficientList =
      F.baseList.map (nativeExteriorCoefficientParameterStalkMap X Y T z hz Z w hw x).hom :=
  (nativeExteriorParameter_map_list X Y T z hz Z w hw x F.baseList).symm

/-- Mapping the base family preserves its length, including the empty family. -/
theorem ambientList_length : F.ambientList.length = F.baseList.length := List.length_map _

/-- The coefficient family has exactly the same ordered index set as the ambient family. -/
theorem coefficientList_length : F.coefficientList.length = F.ambientList.length :=
  List.length_map _

end NativeExteriorParameterStalkFamily
end Stacks.Chow
