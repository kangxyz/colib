/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SingularPresheafFixedPoints
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.IteratedTotalSwap
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalInvariantUnit

/-!
# Reflection into A¹-invariant derived transfer presheaves

The actual singular augmentation is invertible on a bounded-above complex
with invariant cohomology. The exchange of the two simplex factors identifies
the other augmentation after singularization, giving the universal property
by precomposition with the original unit.
-/

public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

private theorem singularTotal_map_unit_quasiIso {k : Type u} [Field k]
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    QuasiIso ((singularTotalFunctor k).map ((singularTotalUnit k).app K)) := by
  let C := singularTotalFunctor k
  let η := singularTotalUnit k
  let L := C.obj K
  let e := iteratedSingularTotalSwap K b
  let : L.IsStrictlyLE b := singularTotalFunctor_obj_isStrictlyLE k K b
  have hη : QuasiIso (η.app L) := singularTotalUnitApp_quasiIso_of_homology L b
    (singularTotalFunctor_homology_isA1Invariant K b)
  have h : QuasiIso (C.map (η.app K) ≫ e.hom) :=
    (singularTotal_map_unit_comp_iteratedSingularTotalSwap K b).symm ▸ hη
  let : QuasiIso (C.map (η.app K) ≫ e.hom) := h
  exact quasiIso_of_comp_right _ e.hom

private theorem bijective_precomp_of_unit {D : Type*} [Category* D]
    (F : D ⥤ D) (η : 𝟭 D ⟶ F) (X Y : D) [IsIso (F.map (η.app X))]
    [IsIso (η.app Y)] : Function.Bijective (fun f : F.obj X ⟶ Y => η.app X ≫ f) := by
  constructor
  · intro f g h
    have hmap := F.congr_map h
    rw [F.map_comp, F.map_comp] at hmap
    have he : F.map f = F.map g := (cancel_epi (F.map (η.app X))).1 hmap
    apply (cancel_mono (η.app Y)).1
    calc
      f ≫ η.app Y = η.app (F.obj X) ≫ F.map f := η.naturality f
      _ = η.app (F.obj X) ≫ F.map g := congrArg (η.app (F.obj X) ≫ ·) he
      _ = g ≫ η.app Y := (η.naturality g).symm
  · intro g
    refine ⟨F.map g ≫ inv (η.app Y), ?_⟩
    have h : g ≫ η.app Y = η.app X ≫ F.map g := η.naturality g
    change η.app X ≫ F.map g ≫ inv (η.app Y) = g
    rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

private theorem isIso_singularPresheafDerivedFunctor_map_unit
    (X : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) :
    IsIso ((singularPresheafDerivedFunctor k).map ((singularPresheafDerivedUnit k).app X)) := by
  obtain ⟨b, hb⟩ := X.property
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_singularPresheafDerivedCochainObj_iso k X b hb
  let : K.IsStrictlyLE b := hK
  let C := singularTotalFunctor k
  let F := singularPresheafDerivedFunctor k
  let η := singularPresheafDerivedUnit k
  let L := C.obj K
  let u₀ := singularTotalUnitApp k K
  let QK := singularPresheafDerivedCochainObj k K b
  let : L.IsStrictlyLE b := singularTotalFunctor_obj_isStrictlyLE k K b
  let : (C.obj L).IsStrictlyLE b := singularTotalFunctor_obj_isStrictlyLE k L b
  let : QuasiIso (C.map u₀) := singularTotal_map_unit_quasiIso K b
  let a := singularPresheafDerivedCochainIso k K b
  let d := singularPresheafDerivedCochainIso k L b
  let t := singularPresheafDerivedCochainMap k (C.map u₀) b b
  let : IsIso t := isIso_singularPresheafDerivedCochainMap_of_quasiIso k (C.map u₀) b b
  have ht : F.map (singularPresheafDerivedCochainMap k u₀ b b) ≫ d.hom = a.hom ≫ t :=
    singularPresheafDerivedCochainIso_naturality k u₀ b b
  have ha : η.app QK ≫ a.hom = singularPresheafDerivedCochainMap k u₀ b b :=
    singularPresheafDerivedCochainIso_unit k K b
  have h : F.map (η.app QK) ≫ (F.map a.hom ≫ d.hom) = a.hom ≫ t := by
    rw [← Category.assoc, ← F.map_comp, ha, ht]
  let : IsIso (F.map (η.app QK) ≫ (F.map a.hom ≫ d.hom)) := h.symm ▸ inferInstance
  let : IsIso (F.map (η.app QK)) := IsIso.of_isIso_comp_right _ (F.map a.hom ≫ d.hom)
  have he₀ : e.hom ≫ η.app X = η.app QK ≫ F.map e.hom := η.naturality e.hom
  have he : F.map e.hom ≫ F.map (η.app X) = F.map (η.app QK) ≫ F.map (F.map e.hom) := by
    rw [← F.map_comp, ← F.map_comp, he₀]
  let : IsIso (F.map e.hom ≫ F.map (η.app X)) := he.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left (F.map e.hom) _

/-- Precomposing with the actual derived augmentation is bijective for an invariant target. -/
theorem bijective_precomp_singularPresheafDerivedUnit
    (X Y : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k))
    (hY : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (PresheafWithTransfers.{u + 1} k) i).obj
      Y.obj).IsA1Invariant) :
    Function.Bijective (fun f : (singularPresheafDerivedFunctor k).obj X ⟶ Y =>
      (singularPresheafDerivedUnit k).app X ≫ f) := by
  let F := singularPresheafDerivedFunctor k
  let η := singularPresheafDerivedUnit k
  let : IsIso (F.map (η.app X)) := isIso_singularPresheafDerivedFunctor_map_unit k X
  let : IsIso (η.app Y) := isIso_singularPresheafDerivedUnit_app k Y hY
  exact bijective_precomp_of_unit F η X Y

end AlgebraicGeometry.MotivicHomotopy
