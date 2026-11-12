/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedPencilEndpoints
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.ConstantFamily

/-!
# The actual whole polynomial family minus the actual constant pole

Both terms are the existing whole finite-flat span construction on literal
native zero schemes. The constant family is constructed from the original pole
by actual Cartesian base change, so its finite flatness is derived rather than
postulated. The two endpoint identities retain the entire original zero schemes.
The family and pole can belong to different invertible modules.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

private theorem nativeSectionSpecialization_sub {k : Type u} [Field k]
    {U W : SmoothSite (Spec (.of k))} {s : k}
    {δ δ' : finiteCorrespondences (affineLineCylinder.obj U).hom W.hom}
    {η η' : finiteCorrespondences U.hom W.hom}
    (h : NativeSectionSpanSpecialization (k := k) U W s δ η)
    (h' : NativeSectionSpanSpecialization (k := k) U W s δ' η') :
    NativeSectionSpanSpecialization (k := k) U W s (δ - δ') (η - η') := by
  unfold NativeSectionSpanSpecialization at h h' ⊢
  rw [Preadditive.comp_sub, h, h']

variable {k : Type u} [Field k] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t] (q : X ⟶ S) (r : V ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  (L P : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property P]
  (a c : Γ(L, ⊤)) (u : Γ(P, ⊤))

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "F" => nativeRetainedFamilySource (k := k) t q r L a c
local notation "FP" => nativeRetainedFamilySource (k := k) t q r P u u

/-- The finite-flat witnesses of the original family and its original pole. -/
structure RetainedPencilWitnesses : Prop where
  familyFinite : IsFinite F
  familyFlat : Flat F
  poleFinite : IsFinite ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)
  poleFlat : Flat ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)

section ConstantFamily

variable [hPoleFin : IsFinite ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)]
  [hPoleFlat : Flat ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)]

omit [IsSeparated t] [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)] hPoleFlat in
/-- The actual constant pole family is finite, by base change of the original whole pole. -/
theorem nativeRetainedConstantSource_isFinite : IsFinite FP := by
  unfold nativeRetainedFamilySource
  have := isFinite_constantFamilySource (q ≫ t) (pullback.fst q r) P u
  infer_instance

omit [IsSeparated t] [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)] hPoleFin in
/-- The actual constant pole family is flat, by base change of the original whole pole. -/
theorem nativeRetainedConstantSource_flat : Flat FP := by
  unfold nativeRetainedFamilySource
  have := flat_constantFamilySource (q ≫ t) (pullback.fst q r) P u
  infer_instance

end ConstantFamily

/-- The polynomial family minus its constant pole, formed from their actual witnesses. -/
def retainedPencilDifferenceFromWitnesses
    (h : RetainedPencilWitnesses (k := k) t q r L P a c u) :
    Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W := by
  let f := F
  let hFin : IsFinite f := h.familyFinite
  let hFlat : Flat f := h.familyFlat
  let familySpan : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W :=
    nativeRetainedFamilySpan (k := k) t q r L a c
      (_hFamilyFin := hFin) (_hFamilyFlat := hFlat)
  let poleSpan : Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W :=
    nativeRetainedFamilySpan (k := k) t q r P u u
      (_hFamilyFin := nativeRetainedConstantSource_isFinite (k := k) t q r P u
        (hPoleFin := h.poleFinite))
      (_hFamilyFlat := nativeRetainedConstantSource_flat (k := k) t q r P u
        (hPoleFlat := h.poleFlat))
  exact familySpan - poleSpan

section PoleWitnesses

variable [hPoleFin : IsFinite ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)]
  [hPoleFlat : Flat ((zeroScheme (pullback q r) P u).subschemeι ≫ pullback.fst q r)]

/-- The genuine whole polynomial-family correspondence minus the genuine constant pole. -/
def retainedPencilDifference :
    let f := F
    ∀ [_hFamilyFin : IsFinite f] [_hFamilyFlat : Flat f],
      Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W := by
  intro f hFin hFlat
  let h : RetainedPencilWitnesses (k := k) t q r L P a c u :=
    ⟨hFin, hFlat, hPoleFin, hPoleFlat⟩
  exact retainedPencilDifferenceFromWitnesses (k := k) t q r L P a c u h

/-- The zero endpoint of the actual difference is the complete original zero
scheme minus the complete original pole, with both literal retained-product legs. -/
theorem retainedPencilDifference_zero :
    let f := F
    ∀ [hFamilyFin : IsFinite f] [hFamilyFlat : Flat f],
      let h := nativeRetainedZero_finite_flat (k := k) t q r L a c
        (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
      NativeSectionSpanSpecialization (k := k) U W 0
        (retainedPencilDifference (k := k) t q r L P a c u
          (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat))
        (retainedZeroSpan (k := k) t q r L a h.1 h.2 -
          retainedZeroSpan (k := k) t q r P u hPoleFin hPoleFlat) := by
  intro f hFin hFlat
  have hLeft := nativeRetainedFamily_zero (k := k) t q r L a c
    (hFamilyFin := hFin) (hFamilyFlat := hFlat)
  have hRight := nativeRetainedFamily_zero (k := k) t q r P u u
    (hFamilyFin := nativeRetainedConstantSource_isFinite (k := k) t q r P u)
    (hFamilyFlat := nativeRetainedConstantSource_flat (k := k) t q r P u)
  exact nativeSectionSpecialization_sub (k := k) hLeft hRight

/-- The one endpoint retains the second complete zero scheme and exactly the
same complete constant pole, with no extra constant-family flatness assumption. -/
theorem retainedPencilDifference_one :
    let f := F
    ∀ [hFamilyFin : IsFinite f] [hFamilyFlat : Flat f],
      let h := nativeRetainedOne_finite_flat (k := k) t q r L a c
        (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
      NativeSectionSpanSpecialization (k := k) U W 1
        (retainedPencilDifference (k := k) t q r L P a c u
          (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat))
        (retainedZeroSpan (k := k) t q r L c h.1 h.2 -
          retainedZeroSpan (k := k) t q r P u hPoleFin hPoleFlat) := by
  intro f hFin hFlat
  have hLeft := nativeRetainedFamily_one (k := k) t q r L a c
    (hFamilyFin := hFin) (hFamilyFlat := hFlat)
  have hRight := nativeRetainedFamily_one (k := k) t q r P u u
    (hFamilyFin := nativeRetainedConstantSource_isFinite (k := k) t q r P u)
    (hFamilyFlat := nativeRetainedConstantSource_flat (k := k) t q r P u)
  exact nativeSectionSpecialization_sub (k := k) hLeft hRight

end PoleWitnesses

/-- The literal zero endpoint of the signed difference from the same witnesses. -/
theorem retainedPencilDifferenceFromWitnesses_zero
    (h : RetainedPencilWitnesses (k := k) t q r L P a c u) :
    let hFiber := nativeRetainedZero_finite_flat (k := k) t q r L a c
      (_hFamilyFin := h.familyFinite) (_hFamilyFlat := h.familyFlat)
    NativeSectionSpanSpecialization (k := k) U W 0
      (retainedPencilDifferenceFromWitnesses (k := k) t q r L P a c u h)
      (retainedZeroSpan (k := k) t q r L a hFiber.1 hFiber.2 -
        retainedZeroSpan (k := k) t q r P u h.poleFinite h.poleFlat) :=
  retainedPencilDifference_zero (k := k) t q r L P a c u
    (hPoleFin := h.poleFinite) (hPoleFlat := h.poleFlat)
    (hFamilyFin := h.familyFinite) (hFamilyFlat := h.familyFlat)

/-- The literal one endpoint of the signed difference from the same witnesses. -/
theorem retainedPencilDifferenceFromWitnesses_one
    (h : RetainedPencilWitnesses (k := k) t q r L P a c u) :
    let hFiber := nativeRetainedOne_finite_flat (k := k) t q r L a c
      (_hFamilyFin := h.familyFinite) (_hFamilyFlat := h.familyFlat)
    NativeSectionSpanSpecialization (k := k) U W 1
      (retainedPencilDifferenceFromWitnesses (k := k) t q r L P a c u h)
      (retainedZeroSpan (k := k) t q r L c hFiber.1 hFiber.2 -
        retainedZeroSpan (k := k) t q r P u h.poleFinite h.poleFlat) :=
  retainedPencilDifference_one (k := k) t q r L P a c u
    (hPoleFin := h.poleFinite) (hPoleFlat := h.poleFlat)
    (hFamilyFin := h.familyFinite) (hFamilyFlat := h.familyFlat)

end AlgebraicGeometry.Cor
