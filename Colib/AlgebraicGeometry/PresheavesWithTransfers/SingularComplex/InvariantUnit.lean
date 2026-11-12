/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.SimplexInvariance
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Unit
public import Colib.AlgebraicTopology.DoldKan.InvertibleFace
import Mathlib.Algebra.Homology.Functor

/-!
# Singularization of A¹-invariant transfer coefficients

For an invariant coefficient every original simplex projection acts
invertibly. Its composite with any coface is the projection in the
preceding degree. Thus the positive Moore terms vanish and the
augmentation computes the original coefficient in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology AlgebraicTopology.NormalizedMooreComplex
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- On invariant coefficients the original singular augmentation is a quasi-isomorphism. -/
theorem singularChainUnitApp_quasiIso (P : PresheafWithTransfers.{v} k)
    (hP : P.IsA1Invariant) : QuasiIso (singularChainUnitApp P) := by
  let U := AdditiveFunctor.forget (Cor k)ᵒᵖ AddCommGrpCat.{v}
  let : U.ReflectsIsomorphisms :=
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v}).fullyFaithfulι.reflectsIsomorphisms
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology (singularChainUnitApp P) U).1
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro X
  let E : PresheafWithTransfers.{v} k ⥤ AddCommGrpCat.{v} :=
    U ⋙ (CategoryTheory.evaluation (Cor k)ᵒᵖ AddCommGrpCat.{v}).obj X
  let S := (Cor.simplexProductCosimplicial X.unop).op ⋙ P.obj
  let L := (E.mapHomologicalComplex (.down ℕ)).obj
    ((ChainComplex.single₀ (PresheafWithTransfers.{v} k)).obj P)
  let e : (ChainComplex.single₀ AddCommGrpCat).obj (E.obj P) ≅ L :=
    ((HomologicalComplex.singleMapHomologicalComplex E (.down ℕ) 0).app P).symm
  let f := (E.mapHomologicalComplex (.down ℕ)).map (singularChainUnitApp P)
  let g : (ChainComplex.single₀ AddCommGrpCat).obj (E.obj P) ⟶
      (alternatingFaceMapComplex AddCommGrpCat).obj S := e.hom ≫ f
  have hterm (n : ℕ) : IsIso (E.map (singularTermUnit P n)) :=
    isIso_transfer_simplexProjection P hP X.unop.toSmoothSite n
  let : IsIso (f.f 0) := by
    change IsIso (E.map ((singularChainUnitApp P).f 0))
    rw [singularChainUnitApp_f_zero]
    exact hterm 0
  let : IsIso (g.f 0) := inferInstanceAs (IsIso (e.hom.f 0 ≫ f.f 0))
  have hg : QuasiIso g := quasiIso_fromSingle_of_mono_faces S _ g fun n => by
    let D := AlgebraicSimplex.smoothSiteObj k (n + 1)
    let D' := AlgebraicSimplex.smoothSiteObj k n
    let b := X.unop.toSmoothSite
    let i : Fin (n + 1) := 0
    let face : SmoothSite.product b D' ⟶ SmoothSite.product b D :=
      SmoothSite.productMap (𝟙 b) ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i.succ)
    let a := (Cor.graphFunctor k).map face
    let p := (Cor.graphFunctor k).map (SmoothSite.productFst b D)
    let q := (Cor.graphFunctor k).map (SmoothSite.productFst b D')
    have hp : a ≫ p = q := by
      have h₀ : face ≫ SmoothSite.productFst b D = SmoothSite.productFst b D' :=
        (SmoothSite.productMap_fst (𝟙 b)
          ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i.succ)).trans (Category.comp_id _)
      exact ((Cor.graphFunctor k).map_comp face (SmoothSite.productFst b D)).symm.trans
        (congrArg (fun m => (Cor.graphFunctor k).map m) h₀)
    have he : transfer P p ≫ transfer P a = transfer P q :=
      (transfer_comp P a p).symm.trans (congrArg (fun m => transfer P m) hp)
    let : IsIso (transfer P p) := hterm (n + 1)
    let : IsIso (transfer P q) := hterm n
    let : IsIso (transfer P a) := IsIso.of_isIso_fac_left he
    exact ⟨i, inferInstanceAs (Mono (transfer P a))⟩
  let : QuasiIso (e.hom ≫ f) := hg
  exact quasiIso_of_comp_left e.hom f

end AlgebraicGeometry.PresheafWithTransfers
