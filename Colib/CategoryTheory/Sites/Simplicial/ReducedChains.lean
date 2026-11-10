/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Ordinary reduced chains of pointed simplicial presheaves

Free abelianization is taken in every simplicial degree and at every object of
the site. Its cokernel on the supplied global basepoint is the reduced free
simplicial abelian presheaf. The chosen chain functor is Mathlib's normalized
Moore complex, which is the forward functor of its abelian Dold–Kan equivalence.

For a topology admitting abelian sheafification, the sheaf construction first
sheafifies in each simplicial degree and then normalizes in the abelian category
of sheaves. This constructs the source of the derived Hom in Voevodsky,
*Reduced power operations in motivic cohomology* (2003), equation (2.9).
The comparison with motivic cohomology requires the local derived comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- Ordinary free abelianization, in each degree and at each site object. -/
def freeAbelian : (Cᵒᵖ ⥤ SSet.{w}) ⥤ SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  (Functor.flipping (C := Cᵒᵖ) (D := SimplexCategoryᵒᵖ) (E := Type w)).functor ⋙
    (Functor.whiskeringRight _ _ _).obj
      ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free)

instance : (freeAbelian.{w} C).IsLeftAdjoint := by
  let adj := (Functor.flipping (C := Cᵒᵖ) (D := SimplexCategoryᵒᵖ) (E := Type w)).toAdjunction.comp
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).whiskerRight SimplexCategoryᵒᵖ)
  exact ⟨_, ⟨adj⟩⟩

@[simp]
theorem freeAbelian_obj_obj_obj (F : Cᵒᵖ ⥤ SSet.{w})
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (((freeAbelian C).obj F).obj n).obj U =
      AddCommGrpCat.of (FreeAbelianGroup ((F.obj U).obj n)) := rfl

@[simp]
theorem freeAbelian_map_app_app {F G : Cᵒᵖ ⥤ SSet.{w}} (f : F ⟶ G)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (((freeAbelian C).map f).app n).app U =
      AddCommGrpCat.free.map ((f.app U).app n) := rfl

/-- The free abelian image of the actual global basepoint. -/
def basepointArrow : PointedSimplicialPresheaf.{w} C ⥤
    Arrow (SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})) where
  obj F := Arrow.mk ((freeAbelian C).map F.hom)
  map f := Arrow.homMk' (𝟙 _) ((freeAbelian C).map f.right) (by
    rw [Category.id_comp, ← Functor.map_comp, Under.w f])
  map_id F := by
    apply Arrow.hom_ext <;> simp [Under.id_right]
  map_comp f g := by
    apply Arrow.hom_ext <;> simp [Under.comp_right]

/-- The ordinary reduced free simplicial abelian presheaf. -/
def reducedFreeAbelian : PointedSimplicialPresheaf.{w} C ⥤
    SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  basepointArrow C ⋙ coker _

/-- Reduction is the cokernel of free abelianization of the supplied point. -/
theorem reducedFreeAbelian_obj (F : PointedSimplicialPresheaf.{w} C) :
    (reducedFreeAbelian C).obj F = cokernel ((freeAbelian C).map F.hom) := rfl

/-- The projection from free abelian chains to reduced free abelian chains. -/
def reduction (F : PointedSimplicialPresheaf.{w} C) :
    (freeAbelian C).obj F.right ⟶ (reducedFreeAbelian C).obj F :=
  cokernel.π ((freeAbelian C).map F.hom)

@[reassoc (attr := simp)]
theorem basepoint_reduction (F : PointedSimplicialPresheaf.{w} C) :
    (freeAbelian C).map F.hom ≫ reduction C F = 0 :=
  cokernel.condition ((freeAbelian C).map F.hom)

@[reassoc (attr := simp)]
theorem reduction_naturality {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G) :
    reduction C F ≫ (reducedFreeAbelian C).map f =
      (freeAbelian C).map f.right ≫ reduction C G :=
  ((coker.π _).naturality ((basepointArrow C).map f)).symm

/-- A map factors uniquely through reduction exactly when it kills the supplied
basepoint after free abelianization. -/
def reductionDesc (F : PointedSimplicialPresheaf.{w} C)
    {A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})}
    (f : (freeAbelian C).obj F.right ⟶ A)
    (h : (freeAbelian C).map F.hom ≫ f = 0) :
    (reducedFreeAbelian C).obj F ⟶ A :=
  cokernel.desc _ f h

@[reassoc (attr := simp)]
theorem reduction_reductionDesc (F : PointedSimplicialPresheaf.{w} C)
    {A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})}
    (f : (freeAbelian C).obj F.right ⟶ A)
    (h : (freeAbelian C).map F.hom ≫ f = 0) :
    reduction C F ≫ reductionDesc C F f h = f :=
  cokernel.π_desc _ _ _

theorem reduction_hom_ext {F : PointedSimplicialPresheaf.{w} C}
    {A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})}
    {f g : (reducedFreeAbelian C).obj F ⟶ A}
    (h : reduction C F ≫ f = reduction C F ≫ g) : f = g :=
  (cancel_epi (cokernel.π ((freeAbelian C).map F.hom))).1 h

instance : (reducedFreeAbelian.{w} C).PreservesZeroMorphisms where
  map_zero F G := by
    apply reduction_hom_ext C
    simp only [reduction_naturality, zero_right, Functor.map_comp, Category.assoc,
      basepoint_reduction, comp_zero]

/-- Evaluation of a simplicial abelian presheaf at one degree and one site object. -/
abbrev abelianEvaluation (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w} :=
  (CategoryTheory.evaluation _ _).obj n ⋙ (CategoryTheory.evaluation _ _).obj U

/-- The raw value is the cokernel of the free map induced by the basepoint in
that exact degree and at that exact site object. -/
def reducedFreeAbelianObjIso (F : PointedSimplicialPresheaf.{w} C)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (((reducedFreeAbelian C).obj F).obj n).obj U ≅
      cokernel (AddCommGrpCat.free.map ((F.hom.app U).app n)) :=
  PreservesCokernel.iso (abelianEvaluation C n U) ((freeAbelian C).map F.hom)

/-- The explicit quotient formula. Only the subgroup generated by the image of
the supplied basepoint is killed. -/
def reducedFreeAbelianObjIsoQuotient (F : PointedSimplicialPresheaf.{w} C)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (((reducedFreeAbelian C).obj F).obj n).obj U ≅
      AddCommGrpCat.of (FreeAbelianGroup ((F.right.obj U).obj n) ⧸
        (AddCommGrpCat.free.map ((F.hom.app U).app n)).hom.range) :=
  reducedFreeAbelianObjIso C F n U ≪≫ AddCommGrpCat.cokernelIsoQuotient _

@[reassoc (attr := simp)]
theorem reduction_comp_reducedFreeAbelianObjIso_hom (F : PointedSimplicialPresheaf.{w} C)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    ((reduction C F).app n).app U ≫ (reducedFreeAbelianObjIso C F n U).hom =
      cokernel.π (AddCommGrpCat.free.map ((F.hom.app U).app n)) :=
  PreservesCokernel.π_iso_hom (abelianEvaluation C n U) ((freeAbelian C).map F.hom)

@[reassoc (attr := simp)]
theorem reduction_comp_reducedFreeAbelianObjIsoQuotient_hom
    (F : PointedSimplicialPresheaf.{w} C) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    ((reduction C F).app n).app U ≫ (reducedFreeAbelianObjIsoQuotient C F n U).hom =
      AddCommGrpCat.ofHom
        (QuotientAddGroup.mk' (AddCommGrpCat.free.map ((F.hom.app U).app n)).hom.range) := by
  change ((reduction C F).app n).app U ≫
    ((reducedFreeAbelianObjIso C F n U).hom ≫ (AddCommGrpCat.cokernelIsoQuotient _).hom) = _
  rw [← Category.assoc, reduction_comp_reducedFreeAbelianObjIso_hom]
  exact cokernel.π_desc (AddCommGrpCat.free.map ((F.hom.app U).app n)) _ _

/-- Each value of the terminal simplicial presheaf has a unique simplex. -/
@[instance_reducible]
def terminalSimplexUnique (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    Unique (((⊤_ (Cᵒᵖ ⥤ SSet.{w})).obj U).obj n) :=
  Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj
    ((CategoryTheory.evaluation Cᵒᵖ SSet.{w}).obj U ⋙ (CategoryTheory.evaluation _ _).obj n) _)

/-- The simplex supplied by the global basepoint. -/
def basepointSimplex (F : PointedSimplicialPresheaf.{w} C)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) : (F.right.obj U).obj n :=
  (F.hom.app U).app n (terminalSimplexUnique C n U).default

/-- The class of a simplex in the reduced free abelian group. -/
def reducedGenerator (F : PointedSimplicialPresheaf.{w} C)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (x : (F.right.obj U).obj n) :
    (((reducedFreeAbelian C).obj F).obj n).obj U :=
  ((reduction C F).app n).app U (FreeAbelianGroup.of x)

@[simp]
theorem reducedGenerator_basepoint (F : PointedSimplicialPresheaf.{w} C)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    reducedGenerator C F n U (basepointSimplex C F n U) = 0 := by
  have h := congrArg (fun f ↦ (f.app n).app U
    (FreeAbelianGroup.of (terminalSimplexUnique C n U).default)) (basepoint_reduction C F)
  simp only [NatTrans.comp_app, freeAbelian_map_app_app, Limits.zero_app] at h
  exact h

@[simp]
theorem reducedFreeAbelian_map_reducedGenerator {F G : PointedSimplicialPresheaf.{w} C}
    (f : F ⟶ G) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (x : (F.right.obj U).obj n) :
    (((reducedFreeAbelian C).map f).app n).app U (reducedGenerator C F n U x) =
      reducedGenerator C G n U ((f.right.app U).app n x) := by
  have h := congrArg (fun g ↦ (g.app n).app U (FreeAbelianGroup.of x))
    (reduction_naturality C f)
  simp only [NatTrans.comp_app, freeAbelian_map_app_app] at h
  exact h

/-- Exactly the designated basepoint simplex has zero generator. -/
theorem reducedGenerator_eq_zero_iff (F : PointedSimplicialPresheaf.{w} C)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (x : (F.right.obj U).obj n) :
    reducedGenerator C F n U x = 0 ↔ x = basepointSimplex C F n U := by
  let _ := terminalSimplexUnique.{w} C n U
  let p := (F.hom.app U).app n
  let b := (terminalSimplexUnique.{w} C n U).default
  let d : AddCommGrpCat.free.obj ((F.right.obj U).obj n) ⟶
      AddCommGrpCat.free.obj ((F.right.obj U).obj n) :=
    AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun y ↦
      FreeAbelianGroup.of y - FreeAbelianGroup.of (p b))
  have hd : AddCommGrpCat.free.map p ≫ d = 0 := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro y
    rw [show y = b from Subsingleton.elim _ _]
    change d ((AddCommGrpCat.free.map p) (FreeAbelianGroup.of b)) = 0
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
    exact (FreeAbelianGroup.lift_apply_of _ _).trans (sub_self _)
  constructor
  · intro hx
    have hq : cokernel.π (AddCommGrpCat.free.map p) (FreeAbelianGroup.of x) = 0 := by
      rw [← reduction_comp_reducedFreeAbelianObjIso_hom C F n U]
      change (reducedFreeAbelianObjIso C F n U).hom (reducedGenerator C F n U x) = 0
      rw [hx, map_zero]
    apply FreeAbelianGroup.of_injective
    apply sub_eq_zero.mp
    let q := cokernel.desc (AddCommGrpCat.free.map p) d hd
    have heq := congrArg (fun f ↦ f (FreeAbelianGroup.of x))
      (cokernel.π_desc (AddCommGrpCat.free.map p) d hd)
    change q (cokernel.π (AddCommGrpCat.free.map p) (FreeAbelianGroup.of x)) =
      d (FreeAbelianGroup.of x) at heq
    rw [hq, map_zero] at heq
    exact (FreeAbelianGroup.lift_apply_of _ _).symm.trans heq.symm
  · rintro rfl
    exact reducedGenerator_basepoint C F n U

private def freeAbelianCofanIsColimit (F : Cᵒᵖ ⥤ SSet.{w}) :
    IsColimit (BinaryCofan.mk ((freeAbelian C).map (freeInclusion C F))
      ((freeAbelian C).map ((free C).obj F).hom)) :=
  isColimitOfHasBinaryCoproductOfPreservesColimit (freeAbelian C) F (⊤_ _)

private def freeReductionIsoApp (F : Cᵒᵖ ⥤ SSet.{w}) :
    (reducedFreeAbelian C).obj ((free C).obj F) ≅ (freeAbelian C).obj F := by
  let H := freeAbelianCofanIsColimit C F
  let p := BinaryCofan.IsColimit.desc H (𝟙 _) 0
  have hl : (freeAbelian C).map (freeInclusion C F) ≫ p = 𝟙 _ :=
    BinaryCofan.IsColimit.inl_desc H _ _
  have hr : (freeAbelian C).map ((free C).obj F).hom ≫ p = 0 :=
    BinaryCofan.IsColimit.inr_desc H _ _
  refine ⟨reductionDesc C _ p hr, (freeAbelian C).map (freeInclusion C F) ≫ reduction C _, ?_, ?_⟩
  · apply reduction_hom_ext C
    simp only [reduction_reductionDesc_assoc, Category.comp_id]
    refine BinaryCofan.IsColimit.hom_ext H ?_ ?_
    · change (freeAbelian C).map (freeInclusion C F) ≫ p ≫ _ =
        (freeAbelian C).map (freeInclusion C F) ≫ reduction C _
      rw [← Category.assoc, hl, Category.id_comp]
    · change (freeAbelian C).map ((free C).obj F).hom ≫ p ≫ _ =
        (freeAbelian C).map ((free C).obj F).hom ≫ reduction C _
      rw [← Category.assoc, hr, zero_comp, basepoint_reduction]
  · rw [Category.assoc, reduction_reductionDesc, hl]

/-- Reduction after freely adjoining a point recovers ordinary free
abelianization. The inverse is induced by the actual coproduct inclusion. -/
@[no_expose]
def freeReducedFreeAbelianIso : free.{w} C ⋙ reducedFreeAbelian C ≅ freeAbelian C :=
  (NatIso.ofComponents (fun F ↦ (freeReductionIsoApp C F).symm) (by
    intro F G f
    change (freeAbelian C).map f ≫ (freeAbelian C).map (freeInclusion C G) ≫ reduction C _ =
      ((freeAbelian C).map (freeInclusion C F) ≫ reduction C _) ≫
        (reducedFreeAbelian C).map ((free C).map f)
    simp only [Category.assoc, reduction_naturality, ← Functor.map_comp_assoc,
      freeInclusion_naturality])).symm

@[simp]
theorem freeReducedFreeAbelianIso_inv_app (F : Cᵒᵖ ⥤ SSet.{w}) :
    (freeReducedFreeAbelianIso C).inv.app F =
      (freeAbelian C).map (freeInclusion C F) ≫ reduction C ((free C).obj F) := by
  unfold freeReducedFreeAbelianIso freeReductionIsoApp
  rfl

/-- Reduced free abelianization of the actual pointed representable agrees
naturally with the free abelianization of the discrete Yoneda presheaf. -/
def yonedaReducedFreeAbelianIso : yoneda C ⋙ reducedFreeAbelian C ≅
    simplicialYoneda C ⋙ freeAbelian C :=
  Functor.isoWhiskerLeft (simplicialYoneda C) (freeReducedFreeAbelianIso C)

/-- Ordinary reduced chains, with the normalized Moore complex as chain model. -/
def reducedChains : PointedSimplicialPresheaf.{w} C ⥤
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ :=
  reducedFreeAbelian C ⋙ AlgebraicTopology.normalizedMooreComplex _

/-- The selected normalization is the forward functor of Mathlib's Dold–Kan
equivalence, without a change of chain model. -/
theorem reducedChains_eq_doldKan : reducedChains.{w} C =
    reducedFreeAbelian C ⋙ (Abelian.DoldKan.equivalence).functor := rfl

section Constant

open AlgebraicTopology

variable {A : Type*} [Category* A] [Abelian A]

private theorem normalizedConst_isZero_succ (M : A) (n : ℕ) :
    IsZero (((normalizedMooreComplex A).obj ((SimplicialObject.const A).obj M)).X (n + 1)) := by
  let X := (SimplicialObject.const A).obj M
  let i : Fin (n + 1) := 0
  change IsZero (NormalizedMooreComplex.objX X (n + 1) : A)
  have h := Subobject.finset_inf_arrow_factors Finset.univ
    (fun k : Fin (n + 1) ↦ kernelSubobject (X.δ k.succ)) i (Finset.mem_univ _)
  have hz : (NormalizedMooreComplex.objX X (n + 1)).arrow ≫ X.δ i.succ = 0 :=
    (kernelSubobject_factors_iff _ _).1 h
  apply IsZero.of_mono_eq_zero (NormalizedMooreComplex.objX X (n + 1)).arrow
  exact (Category.comp_id _).symm.trans hz

private def normalizedConstIsoSingleApp (M : A) :
    (normalizedMooreComplex A).obj ((SimplicialObject.const A).obj M) ≅
      (ChainComplex.single₀ A).obj M := by
  let K := (normalizedMooreComplex A).obj ((SimplicialObject.const A).obj M)
  let e : K.X 0 ≅ M := Subobject.underlyingIso (𝟙 M)
  have h : K.d 1 0 ≫ e.hom = 0 := (normalizedConst_isZero_succ M 0).eq_zero_of_src _
  refine ⟨(ChainComplex.toSingle₀Equiv K M).symm ⟨e.hom, h⟩,
    (ChainComplex.fromSingle₀Equiv K M).symm e.inv, ?_, ?_⟩
  · ext i
    cases i with
    | zero => simp
    | succ i => exact (normalizedConst_isZero_succ M i).eq_of_src _ _
  · apply HomologicalComplex.from_single_hom_ext
    simp

private theorem normalizedConstIsoSingleApp_hom_f_zero (M : A) :
    (normalizedConstIsoSingleApp M).hom.f 0 = (⊤ : Subobject M).arrow := by
  let K := (normalizedMooreComplex A).obj ((SimplicialObject.const A).obj M)
  let f : K.X 0 ⟶ M := (Subobject.underlyingIso (𝟙 M)).hom
  have h : K.d 1 0 ≫ f = 0 := (normalizedConst_isZero_succ M 0).eq_zero_of_src _
  exact (ChainComplex.toSingle₀Equiv_symm_apply_f_zero f h).trans Subobject.underlyingIso_top_hom

private def normalizedConstIsoSingle (A : Type*) [Category* A] [Abelian A] :
    SimplicialObject.const A ⋙ normalizedMooreComplex A ≅ ChainComplex.single₀ A :=
  NatIso.ofComponents normalizedConstIsoSingleApp (by
    intro M N f
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f, Functor.comp_map,
      normalizedConstIsoSingleApp_hom_f_zero, ChainComplex.single₀_map_f_zero]
    exact Subobject.factorThru_arrow (⊤ : Subobject N) ((⊤ : Subobject M).arrow ≫ f)
      (Subobject.top_factors _))

end Constant

/-- Regard an ordinary presheaf of sets as a discrete simplicial presheaf. -/
abbrev discretePresheaf : (Cᵒᵖ ⥤ Type w) ⥤ Cᵒᵖ ⥤ SSet.{w} :=
  (Functor.whiskeringRight _ _ _).obj (Functor.const SimplexCategoryᵒᵖ)

private def discreteReducedFreeAbelianIso :
    discretePresheaf.{w} C ⋙ free C ⋙ reducedFreeAbelian C ≅
      (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free ⋙ SimplicialObject.const _ :=
  Functor.isoWhiskerLeft (discretePresheaf C) (freeReducedFreeAbelianIso C) ≪≫
    (Functor.compConstIso (J := SimplexCategoryᵒᵖ)
      ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free)).symm

/-- Reduced chains of a freely pointed discrete presheaf are its ordinary
free abelian presheaf in degree zero, naturally in the presheaf. -/
@[no_expose]
def discreteReducedChainsIso : discretePresheaf.{w} C ⋙ free C ⋙ reducedChains C ≅
    (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free ⋙ ChainComplex.single₀ _ :=
  Functor.isoWhiskerRight (discreteReducedFreeAbelianIso C)
    (AlgebraicTopology.normalizedMooreComplex _) ≪≫
    Functor.isoWhiskerLeft _ (normalizedConstIsoSingle _)

/-- Reduced chains on the actual pointed representables are the ordinary free
abelian representable presheaves in degree zero. -/
def yonedaReducedChainsIso : yoneda C ⋙ reducedChains C ≅
    CategoryTheory.yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free ⋙
      ChainComplex.single₀ _ :=
  Functor.isoWhiskerLeft CategoryTheory.yoneda (discreteReducedChainsIso C)

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- Reduced free simplicial abelian sheaves, using the actual sheafification
left adjoint in every degree. -/
def sheafifiedReducedFreeAbelian : PointedSimplicialPresheaf.{w} C ⥤
    SimplicialObject (Sheaf J AddCommGrpCat.{w}) :=
  reducedFreeAbelian C ⋙
    (Functor.whiskeringRight _ _ _).obj (presheafToSheaf J AddCommGrpCat.{w})

/-- Sheafify degreewise, then normalize in the abelian category of sheaves. -/
def sheafifiedReducedChains : PointedSimplicialPresheaf.{w} C ⥤
    ChainComplex (Sheaf J AddCommGrpCat.{w}) ℕ :=
  sheafifiedReducedFreeAbelian C J ⋙ AlgebraicTopology.normalizedMooreComplex _

/-- On a freely pointed discrete presheaf, sheafified reduced chains are the
free abelian sheaf on the original presheaf in degree zero. -/
@[no_expose]
def discreteSheafifiedReducedChainsIso :
    discretePresheaf.{w} C ⋙ free C ⋙ sheafifiedReducedChains C J ≅
      (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat.{w} ⋙ ChainComplex.single₀ _ :=
  Functor.isoWhiskerRight (discreteReducedFreeAbelianIso C)
    ((Functor.whiskeringRight _ _ _).obj (presheafToSheaf J AddCommGrpCat.{w}) ⋙
      AlgebraicTopology.normalizedMooreComplex _) ≪≫
    Functor.isoWhiskerLeft ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free)
      (Functor.isoWhiskerRight
      (Functor.compConstIso (J := SimplexCategoryᵒᵖ) (presheafToSheaf J AddCommGrpCat.{w})).symm
      (AlgebraicTopology.normalizedMooreComplex _)) ≪≫
    Functor.isoWhiskerLeft
      ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf J _)
      (normalizedConstIsoSingle _)

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_tag "COL-0389"]
  CategoryTheory.PointedSimplicialPresheaf.sheafifiedReducedChains
  CategoryTheory.PointedSimplicialPresheaf.discreteSheafifiedReducedChainsIso
