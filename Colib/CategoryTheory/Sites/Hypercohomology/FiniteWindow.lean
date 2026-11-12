/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Colib.CategoryTheory.Sites.Hypercohomology.Basic
public import Colib.CategoryTheory.Sites.Hypercohomology.InjectiveTail
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import StacksFrontier.Homology.Ext.CorepresentedHomComplex
import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# A finite lower cutoff for representable hypercohomology

For an object of projective dimension at most `d`, degree-`p` derived Hom out
of that object in degree zero is preserved by the canonical projection to
`τ≥(p-d)`. The lower tail of the truncation triangle vanishes in degrees
`p` and `p+1` by dimension shifting in a termwise injective K-injective model.

For site hypercohomology the representing object is the native free sheaf.
The comparison uses the canonical projection from the given cochain complex
to its good truncation, with its original map in the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Cohomology.Corepresented

universe g w t v u

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] [IsGrothendieckAbelian.{g} A]

/-- The canonical single object has zero shifted derived Hom into a bounded-above
object in degrees above the sum of the bounds. -/
theorem subsingleton_hom_single_shift_of_hasProjectiveDimensionLE
    (P : A) (d : ℕ) [HasProjectiveDimensionLE P d]
    (E : DerivedCategory A) (a : ℤ) [E.IsLE a] (p : ℤ) (hp : a + (d : ℤ) < p) :
    Subsingleton ((singleFunctor A 0).obj P ⟶ E⟦p⟧) := by
  let K := Q.objPreimage E
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj K
  let f := (Stacks.Injectives.kInjectiveResolutionInclusion A).app K
  let : QuasiIso f := inferInstanceAs
    (QuasiIso ((Stacks.Injectives.kInjectiveResolutionInclusion A).app K))
  let : I.IsKInjective := inferInstanceAs
    (((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K).IsKInjective)
  let e : Q.obj I ≅ E := (asIso (Q.map f)).symm ≪≫ Q.objObjPreimageIso E
  let : I.IsLE a := (isLE_Q_obj_iff I a).mp (TStructure.t.isLE_of_iso e.symm a)
  let F := preadditiveCoyoneda.obj (op P)
  have hZero := CochainComplex.isZero_homology_preadditiveCoyoneda_of_exact_tail P I d a
    (fun j _ ↦ inferInstanceAs
      (Injective (((Stacks.Injectives.kInjectiveResolutionFunctor A).obj K).X j)))
    (fun j hj ↦ I.exactAt_of_isLE a j hj) p hp
  let S := (CochainComplex.singleFunctor A 0).obj P
  let eH := (corepresentedHomologyHomotopyAddEquiv F P (Iso.refl F) I p).trans <|
    (AddEquiv.ofBijective Qh.mapAddHom
      (CochainComplex.IsKInjective.Qh_map_bijective
        ((HomotopyCategory.quotient A (.up ℤ)).obj S) (I⟦p⟧))).trans <|
      (CategoryTheory.Linear.homCongr ℤ
        (((quotientCompQhIso A).app S) ≪≫ ((singleFunctorIsoCompQ A 0).app P).symm)
        (((quotientCompQhIso A).app (I⟦p⟧)) ≪≫ (Q.commShiftIso p).app I ≪≫
          (shiftFunctor _ p).mapIso e)).toAddEquiv
  let : Subsingleton (((F.mapHomologicalComplex (.up ℤ)).obj I).homology p) :=
    AddCommGrpCat.subsingleton_of_isZero hZero
  exact eH.symm.injective.subsingleton

private theorem bijective_comp_shift_mor₂_of_hasProjectiveDimensionLE
    (P : A) (d : ℕ) [HasProjectiveDimensionLE P d]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A))
    (a : ℤ) [T.obj₁.IsLE a] (p : ℤ) (hp : a + (d : ℤ) < p) :
    Function.Bijective
      (fun f : (singleFunctor A 0).obj P ⟶ T.obj₂⟦p⟧ ↦ f ≫ T.mor₂⟦p⟧') := by
  let S := (singleFunctor A 0).obj P
  let Tp := (shiftFunctor (Triangle (DerivedCategory A)) p).obj T
  have hTp : Tp ∈ distTriang (DerivedCategory A) := T.shift_distinguished hT p
  have hLeft (f : S ⟶ Tp.obj₁) : f = 0 :=
    (subsingleton_hom_single_shift_of_hasProjectiveDimensionLE P d T.obj₁ a p hp).elim _ _
  have hRight (f : S ⟶ Tp.obj₁⟦(1 : ℤ)⟧) : f = 0 := by
    let e : Tp.obj₁⟦(1 : ℤ)⟧ ≅ T.obj₁⟦p + 1⟧ :=
      (shiftFunctorAdd (DerivedCategory A) p 1).symm.app T.obj₁
    apply (cancel_mono e.hom).mp
    rw [zero_comp]
    exact (subsingleton_hom_single_shift_of_hasProjectiveDimensionLE P d T.obj₁ a
      (p + 1) (by omega)).elim _ _
  constructor
  · intro x y hxy
    change x ≫ T.mor₂⟦p⟧' = y ≫ T.mor₂⟦p⟧' at hxy
    apply sub_eq_zero.mp
    have hz : (x - y) ≫ Tp.mor₂ = 0 := by
      change (x - y) ≫ (p.negOnePow • T.mor₂⟦p⟧') = 0
      rw [Linear.comp_units_smul, Preadditive.sub_comp, hxy, sub_self, smul_zero]
    obtain ⟨f, hf⟩ := Tp.coyoneda_exact₂ hTp (x - y) hz
    have hfZero : f ≫ Tp.mor₁ = 0 := by rw [hLeft f, zero_comp]
    exact hf.trans hfZero
  · intro y
    obtain ⟨x, hx⟩ := Tp.coyoneda_exact₃ hTp y (hRight (y ≫ Tp.mor₃))
    let z : S ⟶ T.obj₂⟦p⟧ := x
    refine ⟨p.negOnePow • z, ?_⟩
    change (p.negOnePow • z) ≫ T.mor₂⟦p⟧' = y
    change y = z ≫ (p.negOnePow • T.mor₂⟦p⟧') at hx
    rw [Linear.units_smul_comp, ← Linear.comp_units_smul]
    exact hx.symm

/-- The canonical derived truncation projection preserves degree-`p` Hom out
of a single object of projective dimension at most `d`. -/
theorem bijective_comp_truncGEπ_of_hasProjectiveDimensionLE
    (P : A) (d : ℕ) [HasProjectiveDimensionLE P d] (E : DerivedCategory A) (p : ℤ) :
    Function.Bijective (fun f : (singleFunctor A 0).obj P ⟶ E⟦p⟧ ↦
      f ≫ ((TStructure.t.truncGEπ (p - (d : ℤ))).app E)⟦p⟧') := by
  let n : ℤ := p - (d : ℤ)
  let T := (TStructure.t.triangleLTGE n).obj E
  let : T.obj₁.IsLE (n - 1) :=
    inferInstanceAs (((TStructure.t.triangleLTGE n).obj E).obj₁.IsLE (n - 1))
  exact bijective_comp_shift_mor₂_of_hasProjectiveDimensionLE P d T
    (TStructure.t.triangleLTGE_distinguished n E) (n - 1) p (by dsimp [n]; omega)

end DerivedCategory

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max v t})]
  [IsGrothendieckAbelian.{g} (Sheaf J AddCommGrpCat.{max v t})]

/-- The actual good truncation map preserves hypercohomology at any site object
whose free representing sheaf has projective dimension at most `d`. -/
theorem isIso_hypercohomologyPresheafFunctor_map_πTruncGE_app
    (X : C) (d : ℕ) [HasProjectiveDimensionLE ((freeYoneda.{t} J).obj X) d]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (p : ℤ) :
    IsIso (((hypercohomologyPresheafFunctor.{w, t} J p).map
      (K.πTruncGE (p - (d : ℤ)))).app (op X)) := by
  let n : ℤ := p - (d : ℤ)
  let F := derivedHomPresheafFunctor.{w, t} J p
  let hS := K.shortComplexTruncLE_shortExact (n - 1)
  let T := DerivedCategory.triangleOfSES hS
  let : T.obj₁.IsLE (n - 1) := by
    change (DerivedCategory.Q.obj (K.truncLE (n - 1))).IsLE (n - 1)
    infer_instance
  let g : K ⟶ (K.shortComplexTruncLE (n - 1)).X₃ := (K.shortComplexTruncLE (n - 1)).g
  let : IsIso ((F.map (DerivedCategory.Q.map g)).app (op X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (DerivedCategory.bijective_comp_shift_mor₂_of_hasProjectiveDimensionLE
        ((freeYoneda.{t} J).obj X) d T (DerivedCategory.triangleOfSES_distinguished hS)
        (n - 1) p (by dsimp [n]; omega))
  have hn : n - 1 + 1 = n := by omega
  let q := K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn
  let : QuasiIso q := inferInstanceAs
    (QuasiIso (K.shortComplexTruncLEX₃ToTruncGE (n - 1) n hn))
  have hcomp : g ≫ q = K.πTruncGE n := K.g_shortComplexTruncLEX₃ToTruncGE (n - 1) n hn
  have hMap : F.map (DerivedCategory.Q.map (K.πTruncGE n)) =
      F.map (DerivedCategory.Q.map g) ≫ F.map (DerivedCategory.Q.map q) := by
    rw [← hcomp]
    exact (congrArg (fun f ↦ F.map f) (DerivedCategory.Q.map_comp g q)).trans
      (F.map_comp (DerivedCategory.Q.map g) (DerivedCategory.Q.map q))
  change IsIso ((F.map (DerivedCategory.Q.map (K.πTruncGE n))).app (op X))
  rw [hMap, NatTrans.comp_app]
  infer_instance

end Stacks.Cohomology.FreeYonedaUnivLE
