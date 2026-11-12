/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Homology.Ext.CorepresentedHomComplex

/-!
# Precomposition for corepresented cohomology

The corepresented Hom complex comparison carries a morphism of representing
objects to its actual precomposition map in the homotopy category.

The degreewise calculation adapts `factorD2` in
`CohomologyPresheafLocallyZero.lean` under
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage` at Stacks
commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
The calculation applies to any cochain complex and any morphism of representing objects.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex Opposite

universe v u

namespace Stacks.Cohomology.Corepresented

variable {A : Type u} [Category.{v} A] [Abelian A]

private theorem homComplexSingleIsoCoyoneda_precomp {P P' : A} (f : P' ⟶ P)
    (I : CochainComplex A ℤ) :
    Locality.precompCM ((CochainComplex.singleFunctor A 0).map f) ≫
        (Locality.homComplexSingleIsoCoyoneda P' I).hom =
      (Locality.homComplexSingleIsoCoyoneda P I).hom ≫
        ((preadditiveCoyoneda.map f.op).mapHomologicalComplex (.up ℤ)).app I := by
  apply HomologicalComplex.hom_ext
  intro j
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  obtain ⟨g, rfl⟩ := Cochain.fromSingleMk_surjective z j (zero_add j)
  change Cochain.fromSingleEquiv (zero_add j)
      ((Cochain.ofHom ((CochainComplex.singleFunctor A 0).map f)).comp
        (Cochain.fromSingleMk g (zero_add j)) (zero_add j)) =
    f ≫ Cochain.fromSingleEquiv (zero_add j) (Cochain.fromSingleMk g (zero_add j))
  rw [← Cochain.fromSingleMk_precomp, Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]

private theorem homComplexHomologyAddEquiv_precomp {K K' I : CochainComplex A ℤ}
    (f : K' ⟶ K) (n : ℤ) (x : (K.HomComplex I).homology n) :
    homComplexHomologyAddEquiv K' I n
        (HomologicalComplex.homologyMap (Locality.precompCM f) n x) =
      (HomotopyCategory.quotient A (.up ℤ)).map f ≫ homComplexHomologyAddEquiv K I n x := by
  obtain ⟨x', rfl⟩ := (homologyAddEquiv K I n).symm.surjective x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x'
  rw [Locality.precompCM_homologyAddEquiv_symm]
  simpa only [homComplexHomologyAddEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply,
    CohomologyClass.homAddEquiv_apply, cohomologyClassPrecomp_mk] using
      toHom_cohomologyClassPrecomp f n (CohomologyClass.mk z)

/-- A map between corepresented functors induces the original precomposition
map on homotopy classes when its comparison square commutes. -/
theorem corepresentedHomologyHomotopyAddEquiv_precomp
    {T T' : A ⥤ AddCommGrpCat.{v}} [T.Additive] [T'.Additive] {P P' : A}
    (e : preadditiveCoyoneda.obj (op P) ≅ T)
    (e' : preadditiveCoyoneda.obj (op P') ≅ T')
    (f : P' ⟶ P) (η : T ⟶ T')
    (h : e.hom ≫ η = preadditiveCoyoneda.map f.op ≫ e'.hom)
    (I : CochainComplex A ℤ) (n : ℤ) (x : ((T.mapHomologicalComplex (.up ℤ)).obj I).homology n) :
    corepresentedHomologyHomotopyAddEquiv T' P' e' I n
        (HomologicalComplex.homologyMap ((η.mapHomologicalComplex (.up ℤ)).app I) n x) =
      (HomotopyCategory.quotient A (.up ℤ)).map ((CochainComplex.singleFunctor A 0).map f) ≫
        corepresentedHomologyHomotopyAddEquiv T P e I n x := by
  let c := ComplexShape.up ℤ
  let S := CochainComplex.singleFunctor A 0
  let Q := HomotopyCategory.quotient A c
  let α := (η.mapHomologicalComplex c).app I
  let β := Locality.precompCM (L := I) (S.map f)
  let a := ((preadditiveCoyoneda.map f.op).mapHomologicalComplex c).app I
  let b := (NatIso.mapHomologicalComplex e c).app I
  let b' := (NatIso.mapHomologicalComplex e' c).app I
  let d := corepresentedHomComplexIso T P e I
  let d' := corepresentedHomComplexIso T' P' e' I
  have hmap : b.hom ≫ α = a ≫ b'.hom := by
    have h' := congr_app (congrArg (fun ξ => NatTrans.mapHomologicalComplex ξ c) h) I
    simp only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] at h'
    exact h'
  have hd : β ≫ d'.hom = d.hom ≫ α := by
    let k := Locality.homComplexSingleIsoCoyoneda P I
    let k' := Locality.homComplexSingleIsoCoyoneda P' I
    change β ≫ (k'.hom ≫ b'.hom) = (k.hom ≫ b.hom) ≫ α
    calc
      _ = (β ≫ k'.hom) ≫ b'.hom := (Category.assoc _ _ _).symm
      _ = (k.hom ≫ a) ≫ b'.hom :=
        congrArg (· ≫ b'.hom) (homComplexSingleIsoCoyoneda_precomp f I)
      _ = k.hom ≫ (a ≫ b'.hom) := Category.assoc _ _ _
      _ = k.hom ≫ (b.hom ≫ α) := congrArg (k.hom ≫ ·) hmap.symm
      _ = _ := (Category.assoc _ _ _).symm
  have hinv : α ≫ d'.inv = d.inv ≫ β := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} c n
  have hH : H.map α ≫ H.map d'.inv = H.map d.inv ≫ H.map β :=
    (H.map_comp _ _).symm.trans ((H.congr_map hinv).trans (H.map_comp _ _))
  have hx := ConcreteCategory.congr_hom hH x
  change H.map d'.inv (H.map α x) = H.map β (H.map d.inv x) at hx
  change homComplexHomologyAddEquiv (S.obj P') I n (H.map d'.inv (H.map α x)) =
    Q.map (S.map f) ≫ homComplexHomologyAddEquiv (S.obj P) I n (H.map d.inv x)
  exact (congrArg (homComplexHomologyAddEquiv (S.obj P') I n) hx).trans
    (homComplexHomologyAddEquiv_precomp (S.map f) n (H.map d.inv x))

end Stacks.Cohomology.Corepresented
