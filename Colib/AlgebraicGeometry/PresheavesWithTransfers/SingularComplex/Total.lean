/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Unit
public import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Total singular complexes of transfer cochain complexes

Apply the original singular construction in each coefficient degree.
The total differential combines the coefficient differential with the
signed simplex differential using Mathlib's cochain totalization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Opposite

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "c" => ComplexShape.up ℤ

local instance (I : Type) : HasColimitsOfShape (Discrete I) (PresheafWithTransfers.{v} k) := by
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{v} :=
    AddCommGrpCat.hasColimitsOfShape
  let : HasColimitsOfShape (Discrete I) ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) :=
    functorCategoryHasColimitsOfShape
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I)
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v})

local instance (K : HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c) :
    K.HasTotal c := fun i =>
  HasColimitsOfShape.has_colimit
    (Discrete.functor (K.toGradedObject.mapObjFun (ComplexShape.π c c c) i))

local instance : (singularCochainFunctor 0 : PresheafWithTransfers.{v} k ⥤
    CochainComplex (PresheafWithTransfers.{v} k) ℤ).Additive := by
  unfold singularCochainFunctor
  infer_instance

/-- The coefficient degree is the first degree of the singular bicomplex. -/
def singularBicomplexFunctor :
    CochainComplex (PresheafWithTransfers.{v} k) ℤ ⥤
      HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c :=
  (singularCochainFunctor 0).mapHomologicalComplex c

/-- The actual total of the singular bicomplex, with the native cochain signs. -/
def singularTotalFunctor :
    CochainComplex (PresheafWithTransfers.{v} k) ℤ ⥤
      CochainComplex (PresheafWithTransfers.{v} k) ℤ :=
  singularBicomplexFunctor k ⋙ HomologicalComplex₂.totalFunctor (PresheafWithTransfers.{v} k) c c c

/-- Each bicomplex column is the existing singular complex in degrees at most zero. -/
@[simp]
theorem singularBicomplexFunctor_obj_X (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ)
    (p : ℤ) :
    ((singularBicomplexFunctor k).obj K).X p = singularCochainComplex (K.X p) 0 := rfl

/-- The total complex preserves the given upper bound on coefficient degrees. -/
theorem singularTotalFunctor_obj_isStrictlyLE (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ)
    (n : ℤ) [K.IsStrictlyLE n] : ((singularTotalFunctor k).obj K).IsStrictlyLE n := by
  apply (CochainComplex.isStrictlyLE_iff _ n).2
  intro i hi
  apply (IsZero.iff_id_eq_zero _).2
  change 𝟙 ((((singularBicomplexFunctor k).obj K).total c).X i) = 0
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p + q = i at hpq
  have hzero : IsZero ((singularCochainComplex (K.X p) 0).X q) := by
    by_cases hq : 0 < q
    · exact isZero_singularCochainComplex_X _ 0 q hq
    · have hp : n < p := by omega
      let ev := singularCochainFunctor (k := k) 0 ⋙
        HomologicalComplex.eval (PresheafWithTransfers.{v} k) c q
      exact ev.map_isZero (K.isZero_of_isStrictlyLE n p hp)
  exact hzero.eq_of_src _ _

variable {k}

/-- The degree-zero inclusion of the original coefficient in its singular cochains. -/
abbrev singularZeroInclusion (P : PresheafWithTransfers.{v} k) :
    P ⟶ (singularCochainComplex P 0).X 0 :=
  singularTermUnit P 0 ≫ (singularCochainXIso P 0 0).inv

@[reassoc]
theorem singularZeroInclusion_naturality {P Q : PresheafWithTransfers.{v} k} (f : P ⟶ Q) :
    f ≫ singularZeroInclusion Q =
      singularZeroInclusion P ≫ ((singularCochainFunctor 0).map f).f 0 := by
  let u := singularTermUnit P 0
  let v := singularTermUnit Q 0
  let e := singularCochainXIso P 0 0
  let j := singularCochainXIso Q 0 0
  let g := (singularComplexMap f).f 0
  rw [singularCochainFunctor_map_f_zero]
  change f ≫ v ≫ j.inv = (u ≫ e.inv) ≫ e.hom ≫ g ≫ j.inv
  calc
    _ = (f ≫ v) ≫ j.inv := (Category.assoc f v j.inv).symm
    _ = (u ≫ g) ≫ j.inv :=
      congrArg (fun m => m ≫ j.inv) (singularTermUnit_naturality f 0)
    _ = u ≫ g ≫ j.inv := Category.assoc u g j.inv
    _ = u ≫ e.inv ≫ e.hom ≫ g ≫ j.inv :=
      congrArg (fun m => u ≫ m) (e.inv_hom_id_assoc (g ≫ j.inv)).symm
    _ = _ := (Category.assoc u e.inv _).symm

variable (k)

/-- Insert the actual degree-zero simplex map in each coefficient degree. -/
def singularTotalUnitApp (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) :
    K ⟶ (singularTotalFunctor k).obj K where
  f i := singularZeroInclusion (K.X i) ≫
    ((singularBicomplexFunctor k).obj K).ιTotal c i 0 i (add_zero i)
  comm' i j h := by
    let B := (singularBicomplexFunctor k).obj K
    let ι (p : ℤ) := B.ιTotal c p 0 p (add_zero p)
    have hv : (B.X i).d 0 1 = 0 :=
      (isZero_singularCochainComplex_X (K.X i) 0 1 (by decide)).eq_of_tgt _ _
    have hd : ι i ≫ (B.total c).d i j = (B.d i j).f 0 ≫ ι j := by
      change ι i ≫ (B.D₁ c i j + B.D₂ c i j) = _
      rw [Preadditive.comp_add, B.ι_D₁, B.ι_D₂,
        B.d₁_eq c h 0 j (add_zero j),
        B.d₂_eq' c i (show (ComplexShape.up ℤ).Rel 0 1 from rfl) j]
      simp only [show ComplexShape.ε₁ c c c (i, 0) = 1 from rfl, one_smul,
        hv, zero_comp, smul_zero, add_zero]
      rfl
    let a (p : ℤ) : K.X p ⟶ (B.X p).X 0 := singularZeroInclusion (K.X p)
    have h₀ : K.d i j ≫ a j = a i ≫ (B.d i j).f 0 :=
      singularZeroInclusion_naturality (K.d i j)
    change (a i ≫ ι i) ≫ (B.total c).d i j = K.d i j ≫ a j ≫ ι j
    calc
      _ = a i ≫ ι i ≫ (B.total c).d i j := Category.assoc _ _ _
      _ = a i ≫ (B.d i j).f 0 ≫ ι j := congrArg (fun m => a i ≫ m) hd
      _ = (a i ≫ (B.d i j).f 0) ≫ ι j := (Category.assoc _ _ _).symm
      _ = (K.d i j ≫ a j) ≫ ι j := congrArg (fun m => m ≫ ι j) h₀.symm
      _ = _ := Category.assoc _ _ _

/-- The natural unit for the total singular construction on transfer complexes. -/
def singularTotalUnit : 𝟭 (CochainComplex (PresheafWithTransfers.{v} k) ℤ) ⟶
    singularTotalFunctor k where
  app := singularTotalUnitApp k
  naturality K L f := by
    ext i : 1
    let B := (singularBicomplexFunctor k).obj K
    let C := (singularBicomplexFunctor k).obj L
    let g : B ⟶ C := (singularBicomplexFunctor k).map f
    let a : K.X i ⟶ (B.X i).X 0 := singularZeroInclusion (K.X i)
    let b : L.X i ⟶ (C.X i).X 0 := singularZeroInclusion (L.X i)
    let ι := B.ιTotal c i 0 i (add_zero i)
    let j := C.ιTotal c i 0 i (add_zero i)
    let m := (HomologicalComplex₂.total.map g c).f i
    have h₀ : f.f i ≫ b = a ≫ (g.f i).f 0 := singularZeroInclusion_naturality (f.f i)
    have h₁ : ι ≫ m = (g.f i).f 0 ≫ j :=
      HomologicalComplex₂.ιTotal_map B C g c i 0 i (add_zero i)
    change f.f i ≫ b ≫ j = (a ≫ ι) ≫ m
    calc
      _ = (f.f i ≫ b) ≫ j := (Category.assoc _ _ _).symm
      _ = (a ≫ (g.f i).f 0) ≫ j := congrArg (fun e => e ≫ j) h₀
      _ = a ≫ (g.f i).f 0 ≫ j := Category.assoc _ _ _
      _ = a ≫ ι ≫ m := congrArg (fun e => a ≫ e) h₁.symm
      _ = _ := (Category.assoc _ _ _).symm

end AlgebraicGeometry.PresheafWithTransfers
