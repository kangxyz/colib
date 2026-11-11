/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Colib.CategoryTheory.Sites.Simplicial.ReducedConeChains

/-!
# Realizing chain homotopies on the pointed simplicial cylinder

In each degree the first vertex of the interval simplex selects either
zero or the original simplex generator. The resulting map respects the
collapsed axis and the reduced free abelianization. The normalized weights
extend a chain homotopy to a map out of the sheafified reduced chains of
the pointed cylinder.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

namespace ReducedCylinderChains

variable (X : PointedSimplicialPresheaf.{w} C)

/-- The actual product before collapsing the basepoint axis. -/
abbrev cylinderProduct := X.right ⨯ interval.{w} C

/-- The chosen pointed cylinder with the constant simplicial interval. -/
abbrev cylinder := parameterizedCylinder X (interval.{w} C)

/-- The reduced free abelian presheaf in the indicated simplicial degree. -/
abbrev reducedAt (m : SimplexCategoryᵒᵖ) :=
  ((reducedFreeAbelian C).obj X).obj m

variable (C) in
/-- The ordinary free abelian presheaf in the given simplicial degree. -/
abbrev freeAt (m : SimplexCategoryᵒᵖ) :
    (Cᵒᵖ ⥤ SSet.{w}) ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  freeAbelian C ⋙ (CategoryTheory.evaluation _ _).obj m

theorem freeAt_map_generator {P Q : Cᵒᵖ ⥤ SSet.{w}} (f : P ⟶ Q)
    (m : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (x : (P.obj U).obj m) :
    (((freeAt C m).map f).app U) (FreeAbelianGroup.of x) =
      FreeAbelianGroup.of ((f.app U).app m x) := by
  change (((freeAbelian C).map f).app m).app U (FreeAbelianGroup.of x) = _
  rw [freeAbelian_map_app_app]
  change FreeAbelianGroup.map ((f.app U).app m) (FreeAbelianGroup.of x) = _
  exact FreeAbelianGroup.map_of _ _

theorem freeAt_hom_ext {P : Cᵒᵖ ⥤ SSet.{w}} {A : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    {m : SimplexCategoryᵒᵖ} {f g : (freeAt C m).obj P ⟶ A}
    (h : ∀ (U : Cᵒᵖ) (x : (P.obj U).obj m),
      f.app U (FreeAbelianGroup.of x) = g.app U (FreeAbelianGroup.of x)) : f = g := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  exact h U x

theorem reducedGenerator_restriction {U V : Cᵒᵖ} (f : U ⟶ V)
    (m : SimplexCategoryᵒᵖ) (x : (X.right.obj U).obj m) :
    (reducedAt X m).map f (reducedGenerator C X m U x) =
      reducedGenerator C X m V ((X.right.map f).app m x) := by
  have h := congrArg (fun a => a (FreeAbelianGroup.of x)) (((reduction C X).app m).naturality f)
  change ((reduction C X).app m).app V
      ((AddCommGrpCat.free.map ((X.right.map f).app m)) (FreeAbelianGroup.of x)) =
    (reducedAt X m).map f (reducedGenerator C X m U x) at h
  rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of] at h
  exact h.symm

theorem presheafMap_apply_naturality {P Q : Cᵒᵖ ⥤ SSet.{w}} (f : P ⟶ Q)
    {U V : Cᵒᵖ} (r : U ⟶ V) (m : SimplexCategoryᵒᵖ) (x : (P.obj U).obj m) :
    (f.app V).app m ((P.map r).app m x) = (Q.map r).app m ((f.app U).app m x) :=
  congrArg (fun a => a.app m x) (f.naturality r)

/-- The generator value weighted by the first vertex of the parameter simplex. -/
def selectedGenerator (m : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (z : ((cylinderProduct X).obj U).obj m) : (reducedAt X m).obj U :=
  if SSet.stdSimplex.asOrderHom
    (((prod.snd : cylinderProduct X ⟶ interval.{w} C).app U).app m z) 0 = 0 then 0
  else reducedGenerator C X m U (((prod.fst : cylinderProduct X ⟶ X.right).app U).app m z)

theorem selectedGenerator_naturality {U V : Cᵒᵖ} (f : U ⟶ V)
    (m : SimplexCategoryᵒᵖ) (z : ((cylinderProduct X).obj U).obj m) :
    selectedGenerator X m V (((cylinderProduct X).map f).app m z) =
      (reducedAt X m).map f (selectedGenerator X m U z) := by
  have ht :
      ((prod.snd : cylinderProduct X ⟶ interval.{w} C).app V).app m
          (((cylinderProduct X).map f).app m z) =
        ((prod.snd : cylinderProduct X ⟶ interval.{w} C).app U).app m z :=
    presheafMap_apply_naturality prod.snd f m z
  unfold selectedGenerator
  rw [ht, presheafMap_apply_naturality (prod.fst : cylinderProduct X ⟶ X.right)]
  split
  · rw [map_zero]
  · exact (reducedGenerator_restriction X f m _).symm

/-- The degreewise weight map on the free abelian presheaf of the product. -/
def productSelector (m : SimplexCategoryᵒᵖ) :
    (freeAt C m).obj (cylinderProduct X) ⟶ reducedAt X m where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (selectedGenerator X m U))
  naturality U V f := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro z
    change FreeAbelianGroup.lift (selectedGenerator X m V)
        ((AddCommGrpCat.free.map (((cylinderProduct X).map f).app m)) (FreeAbelianGroup.of z)) =
      (reducedAt X m).map f
        (FreeAbelianGroup.lift (selectedGenerator X m U) (FreeAbelianGroup.of z))
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
    exact selectedGenerator_naturality X f m z

theorem productSelector_generator (m : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (z : ((cylinderProduct X).obj U).obj m) :
    (productSelector X m).app U (FreeAbelianGroup.of z) = selectedGenerator X m U z :=
  FreeAbelianGroup.lift_apply_of _ _

/-- The original product slice used by the pointed cylinder section. -/
abbrev productSection (i : Fin 2) : X.right ⟶ cylinderProduct X :=
  prod.lift (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C i)

theorem productSection_fst_apply (i : Fin 2) (m : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : (X.right.obj U).obj m) :
    ((prod.fst : cylinderProduct X ⟶ X.right).app U).app m
      (((productSection X i).app U).app m x) = x :=
  congrArg (fun f : X.right ⟶ X.right => (f.app U).app m x)
    (prod.lift_fst (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C i))

theorem productSection_snd_apply (i : Fin 2) (m : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : (X.right.obj U).obj m) :
    ((prod.snd : cylinderProduct X ⟶ interval.{w} C).app U).app m
      (((productSection X i).app U).app m x) =
    ((intervalEndpoint C i).app U).app m (((terminal.from X.right).app U).app m x) :=
  congrArg (fun f : X.right ⟶ interval.{w} C => (f.app U).app m x)
    (prod.lift_snd (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C i))

theorem endpoint_zero_firstVertex (m : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : ((⊤_ (Cᵒᵖ ⥤ SSet.{w})).obj U).obj m) :
    SSet.stdSimplex.asOrderHom (((intervalEndpoint C (1 : Fin 2)).app U).app m x) 0 = 0 := by
  change SSet.stdSimplex.asOrderHom
    ((SSet.stdSimplex.δ (1 : Fin 2)).app m ((SSet.stdSimplex.isTerminalObj₀.from _).app m x)) 0 = 0
  rw [SSet.stdSimplex.δ_one_eq_const]
  rfl

theorem endpoint_one_firstVertex (m : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : ((⊤_ (Cᵒᵖ ⥤ SSet.{w})).obj U).obj m) :
    SSet.stdSimplex.asOrderHom (((intervalEndpoint C (0 : Fin 2)).app U).app m x) 0 = 1 := by
  change SSet.stdSimplex.asOrderHom
    ((SSet.stdSimplex.δ (0 : Fin 2)).app m ((SSet.stdSimplex.isTerminalObj₀.from _).app m x)) 0 = 1
  rw [SSet.stdSimplex.δ_zero_eq_const]
  rfl

theorem productSelector_zero (m : SimplexCategoryᵒᵖ) :
    (freeAt C m).map (productSection X (1 : Fin 2)) ≫ productSelector X m = 0 := by
  apply freeAt_hom_ext
  intro U x
  change (productSelector X m).app U
    (((freeAt C m).map (productSection X (1 : Fin 2))).app U (FreeAbelianGroup.of x)) = 0
  rw [freeAt_map_generator, productSelector_generator]
  unfold selectedGenerator
  rw [productSection_snd_apply, endpoint_zero_firstVertex, ite_eq_left rfl]

theorem productSelector_one (m : SimplexCategoryᵒᵖ) :
    (freeAt C m).map (productSection X (0 : Fin 2)) ≫ productSelector X m =
      (reduction C X).app m := by
  apply freeAt_hom_ext
  intro U x
  change (productSelector X m).app U
      (((freeAt C m).map (productSection X (0 : Fin 2))).app U (FreeAbelianGroup.of x)) =
    reducedGenerator C X m U x
  rw [freeAt_map_generator, productSelector_generator]
  unfold selectedGenerator
  rw [productSection_snd_apply, endpoint_one_firstVertex,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0), productSection_fst_apply]

theorem intervalAxis_fst_apply (m : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : ((interval.{w} C).obj U).obj m) :
    ((prod.fst : cylinderProduct X ⟶ X.right).app U).app m
      (((intervalAxis X (interval.{w} C)).app U).app m x) = basepointSimplex C X m U := by
  have h := congrArg (fun f : interval.{w} C ⟶ X.right => (f.app U).app m x)
    (prod.lift_fst (terminal.from (interval.{w} C) ≫ X.hom) (𝟙 (interval.{w} C)))
  change ((prod.fst : cylinderProduct X ⟶ X.right).app U).app m
      (((intervalAxis X (interval.{w} C)).app U).app m x) =
    (X.hom.app U).app m (((terminal.from (interval.{w} C)).app U).app m x) at h
  let : Unique (((⊤_ (Cᵒᵖ ⥤ SSet.{w})).obj U).obj m) := terminalSimplexUnique C m U
  exact h.trans (congrArg (fun t => (X.hom.app U).app m t) (Subsingleton.elim _ _))

theorem productSelector_axis (m : SimplexCategoryᵒᵖ) :
    (freeAt C m).map (intervalAxis X (interval.{w} C)) ≫ productSelector X m = 0 := by
  apply freeAt_hom_ext
  intro U x
  change (productSelector X m).app U
    (((freeAt C m).map (intervalAxis X (interval.{w} C))).app U (FreeAbelianGroup.of x)) = 0
  rw [freeAt_map_generator, productSelector_generator]
  unfold selectedGenerator
  rw [intervalAxis_fst_apply, reducedGenerator_basepoint]
  split <;> rfl

/-- The original quotient map from the product to the underlying cylinder. -/
abbrev productToCylinder : cylinderProduct X ⟶ (cylinder X).right :=
  pushout.inl (intervalAxis X (interval.{w} C)) (terminal.from (interval.{w} C))

theorem freeAt_cylinder_isPushout (m : SimplexCategoryᵒᵖ) :
    IsPushout ((freeAt C m).map (intervalAxis X (interval.{w} C)))
      ((freeAt C m).map (terminal.from (interval.{w} C)))
      ((freeAt C m).map (productToCylinder X)) ((freeAt C m).map (cylinder X).hom) := by
  let I := interval.{w} C
  let t : I ⟶ (⊤_ (Cᵒᵖ ⥤ SSet.{w})) := terminal.from I
  have h : IsPushout (intervalAxis X I) t (productToCylinder X) (cylinder X).hom :=
    IsPushout.of_hasPushout (intervalAxis X I) t
  let F := freeAt C m
  let : PreservesColimit (span (intervalAxis X I) t) F := by
    change PreservesColimit _ (freeAbelian C ⋙ (CategoryTheory.evaluation _ _).obj m)
    infer_instance
  change IsPushout (F.map (intervalAxis X I)) (F.map t)
    (F.map (productToCylinder X)) (F.map (cylinder X).hom)
  exact F.map_isPushout h

/-- The weight map after collapsing the original point axis. -/
def freeCylinderSelector (m : SimplexCategoryᵒᵖ) :
    (freeAt C m).obj (cylinder X).right ⟶ reducedAt X m :=
  (freeAt_cylinder_isPushout X m).desc (productSelector X m) 0
    (by rw [productSelector_axis, comp_zero])

@[reassoc]
theorem productToCylinder_comp_freeCylinderSelector (m : SimplexCategoryᵒᵖ) :
    (freeAt C m).map (productToCylinder X) ≫ freeCylinderSelector X m = productSelector X m :=
  (freeAt_cylinder_isPushout X m).inl_desc _ _ _

theorem freeCylinderSelector_point (m : SimplexCategoryᵒᵖ) :
    (freeAt C m).map (cylinder X).hom ≫ freeCylinderSelector X m = 0 :=
  (freeAt_cylinder_isPushout X m).inr_desc _ _ _

/-- The first-vertex weight on the actual reduced abelian cylinder degree. -/
def reducedSelector (m : SimplexCategoryᵒᵖ) :
    reducedAt (cylinder X) m ⟶ reducedAt X m :=
  (CokernelCofork.IsColimit.desc' (ReducedConeChains.reductionIsCokernel (cylinder X) m)
    (freeCylinderSelector X m) (freeCylinderSelector_point X m)).1

theorem reduction_comp_reducedSelector (m : SimplexCategoryᵒᵖ) :
    (reduction C (cylinder X)).app m ≫ reducedSelector X m = freeCylinderSelector X m :=
  (CokernelCofork.IsColimit.desc' (ReducedConeChains.reductionIsCokernel (cylinder X) m)
    (freeCylinderSelector X m) (freeCylinderSelector_point X m)).2

theorem freeCylinderSelector_section (i : Fin 2) (m : SimplexCategoryᵒᵖ) :
    (freeAt C m).map (cylinderSection X (intervalEndpoint C i)).right ≫
        freeCylinderSelector X m =
      (freeAt C m).map (productSection X i) ≫ productSelector X m := by
  change (freeAt C m).map (productSection X i ≫ productToCylinder X) ≫
      freeCylinderSelector X m = _
  rw [Functor.map_comp, Category.assoc, productToCylinder_comp_freeCylinderSelector]

@[reassoc]
theorem reduction_app_map {A B : PointedSimplicialPresheaf.{w} C}
    (f : A ⟶ B) (m : SimplexCategoryᵒᵖ) :
    (reduction C A).app m ≫ ((reducedFreeAbelian C).map f).app m =
      (freeAt C m).map f.right ≫ (reduction C B).app m :=
  congr_app (reduction_naturality C f) m

/-- The weight at the first endpoint is zero. -/
theorem reducedSelector_zero (m : SimplexCategoryᵒᵖ) :
    ((reducedFreeAbelian C).map (cylinderSection X (intervalEndpoint C (1 : Fin 2)))).app m ≫
      reducedSelector X m = 0 := by
  apply Cofork.IsColimit.hom_ext (ReducedConeChains.reductionIsCokernel X m)
  change (reduction C X).app m ≫ _ = (reduction C X).app m ≫ _
  rw [reduction_app_map_assoc, reduction_comp_reducedSelector]
  change (freeAt C m).map (cylinderSection X (intervalEndpoint C (1 : Fin 2))).right ≫
    freeCylinderSelector X m = (reduction C X).app m ≫ 0
  rw [freeCylinderSelector_section, productSelector_zero, comp_zero]

/-- The weight at the last endpoint is the identity. -/
theorem reducedSelector_one (m : SimplexCategoryᵒᵖ) :
    ((reducedFreeAbelian C).map (cylinderSection X (intervalEndpoint C (0 : Fin 2)))).app m ≫
      reducedSelector X m = 𝟙 _ := by
  apply Cofork.IsColimit.hom_ext (ReducedConeChains.reductionIsCokernel X m)
  change (reduction C X).app m ≫ _ = (reduction C X).app m ≫ _
  rw [reduction_app_map_assoc, reduction_comp_reducedSelector]
  change (freeAt C m).map (cylinderSection X (intervalEndpoint C (0 : Fin 2))).right ≫
    freeCylinderSelector X m = (reduction C X).app m ≫ 𝟙 _
  rw [freeCylinderSelector_section, productSelector_one, Category.comp_id]

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- The first-vertex weight after degreewise abelian sheafification. -/
def sheafifiedSelector (m : SimplexCategoryᵒᵖ) :
    ((sheafifiedReducedFreeAbelian C J).obj (cylinder X)).obj m ⟶
      ((sheafifiedReducedFreeAbelian C J).obj X).obj m :=
  (presheafToSheaf J AddCommGrpCat.{w}).map (reducedSelector X m)

@[reassoc]
theorem sheafifiedSelector_zero (m : SimplexCategoryᵒᵖ) :
    ((sheafifiedReducedFreeAbelian C J).map
        (cylinderSection X (intervalEndpoint C (1 : Fin 2)))).app m ≫
      sheafifiedSelector X J m = 0 := by
  let L := presheafToSheaf J AddCommGrpCat.{w}
  change L.map (((reducedFreeAbelian C).map
        (cylinderSection X (intervalEndpoint C (1 : Fin 2)))).app m) ≫
      L.map (reducedSelector X m) = 0
  rw [← Functor.map_comp, reducedSelector_zero, Functor.map_zero]

@[reassoc]
theorem sheafifiedSelector_one (m : SimplexCategoryᵒᵖ) :
    ((sheafifiedReducedFreeAbelian C J).map
        (cylinderSection X (intervalEndpoint C (0 : Fin 2)))).app m ≫
      sheafifiedSelector X J m = 𝟙 _ := by
  let L := presheafToSheaf J AddCommGrpCat.{w}
  change L.map (((reducedFreeAbelian C).map
        (cylinderSection X (intervalEndpoint C (0 : Fin 2)))).app m) ≫
      L.map (reducedSelector X m) = 𝟙 _
  rw [← Functor.map_comp, reducedSelector_one, Functor.map_id]

open AlgebraicTopology in
theorem sheafifiedInclusion_naturality {Y Z : PointedSimplicialPresheaf.{w} C}
    (f : Y ⟶ Z) (n : ℕ) :
    ((sheafifiedReducedChains C J).map f).f n ≫
      (inclusionOfMooreComplexMap ((sheafifiedReducedFreeAbelian C J).obj Z)).f n =
    (inclusionOfMooreComplexMap ((sheafifiedReducedFreeAbelian C J).obj Y)).f n ≫
      ((sheafifiedReducedFreeAbelian C J).map f).app (op ⦋n⦌) :=
  congrArg (fun φ => φ.f n) ((inclusionOfMooreComplex _).naturality
    ((sheafifiedReducedFreeAbelian C J).map f))

open AlgebraicTopology in
/-- The first-vertex weight on normalized Moore degrees, using the native inclusion
and retraction between the normalized and alternating face complexes. -/
def normalizedWeight (n : ℕ) :
    ((sheafifiedReducedChains C J).obj (cylinder X)).X n ⟶
      ((sheafifiedReducedChains C J).obj X).X n :=
  (inclusionOfMooreComplexMap ((sheafifiedReducedFreeAbelian C J).obj (cylinder X))).f n ≫
    sheafifiedSelector X J (op ⦋n⦌) ≫
      (DoldKan.PInftyToNormalizedMooreComplex ((sheafifiedReducedFreeAbelian C J).obj X)).f n

open AlgebraicTopology in
theorem normalizedWeight_section (i : Fin 2) (n : ℕ) :
    ((sheafifiedReducedChains C J).map
        (cylinderSection X (intervalEndpoint C i))).f n ≫ normalizedWeight X J n =
      (inclusionOfMooreComplexMap ((sheafifiedReducedFreeAbelian C J).obj X)).f n ≫
        (((sheafifiedReducedFreeAbelian C J).map
          (cylinderSection X (intervalEndpoint C i))).app (op ⦋n⦌) ≫
          sheafifiedSelector X J (op ⦋n⦌)) ≫
        (DoldKan.PInftyToNormalizedMooreComplex
          ((sheafifiedReducedFreeAbelian C J).obj X)).f n := by
  let E := sheafifiedReducedFreeAbelian C J
  let f := cylinderSection X (intervalEndpoint C i)
  let r := (DoldKan.PInftyToNormalizedMooreComplex (E.obj X)).f n
  let s := sheafifiedSelector X J (op ⦋n⦌)
  let p := (inclusionOfMooreComplexMap (E.obj X)).f n
  unfold normalizedWeight
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ s ≫ r) (sheafifiedInclusion_naturality J f n)).trans ?_)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => p ≫ k) (Category.assoc _ _ _).symm)

@[reassoc]
theorem normalizedWeight_zero (n : ℕ) :
    ((sheafifiedReducedChains C J).map
        (cylinderSection X (intervalEndpoint C (1 : Fin 2)))).f n ≫
      normalizedWeight X J n = 0 := by
  rw [normalizedWeight_section, sheafifiedSelector_zero, zero_comp, comp_zero]
  rfl

open AlgebraicTopology in
@[reassoc]
theorem normalizedWeight_one (n : ℕ) :
    ((sheafifiedReducedChains C J).map
        (cylinderSection X (intervalEndpoint C (0 : Fin 2)))).f n ≫
      normalizedWeight X J n = 𝟙 _ := by
  rw [normalizedWeight_section, sheafifiedSelector_one]
  let E := (sheafifiedReducedFreeAbelian C J).obj X
  let p := (inclusionOfMooreComplexMap E).f n
  let r := (DoldKan.PInftyToNormalizedMooreComplex E).f n
  change p ≫ (𝟙 _ ≫ r) = 𝟙 _
  exact (congrArg (fun k => p ≫ k) (Category.id_comp r)).trans
    (congrArg (fun f => f.f n) (DoldKan.splitMonoInclusionOfMooreComplexMap E).id)

end ReducedCylinderChains

variable (X : PointedSimplicialPresheaf.{w} C)
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
  {K : ChainComplex (Sheaf J AddCommGrpCat.{w}) ℕ}
  {a b : (sheafifiedReducedChains C J).obj X ⟶ K}

/-- A chain homotopy induces a chain map from the sheafified reduced normalized
chains of the pointed simplicial cylinder. -/
def sheafifiedReducedCylinderChainsMap (H : Homotopy a b) :
    (sheafifiedReducedChains C J).obj (ReducedCylinderChains.cylinder X) ⟶ K :=
  (sheafifiedReducedChains C J).map (cylinderProjection X (interval.{w} C)) ≫ a +
    Homotopy.nullHomotopicMap
      (fun i j => ReducedCylinderChains.normalizedWeight X J i ≫ H.symm.hom i j)

private theorem section_sheafifiedReducedCylinderChainsMap (H : Homotopy a b) (e : Fin 2) :
    (sheafifiedReducedChains C J).map (cylinderSection X (intervalEndpoint C e)) ≫
      sheafifiedReducedCylinderChainsMap X J H =
    a + Homotopy.nullHomotopicMap (fun i j =>
      ((sheafifiedReducedChains C J).map (cylinderSection X (intervalEndpoint C e))).f i ≫
        ReducedCylinderChains.normalizedWeight X J i ≫ H.symm.hom i j) := by
  rw [sheafifiedReducedCylinderChainsMap, Preadditive.comp_add, ← Category.assoc,
    ← Functor.map_comp, cylinderSection_projection, Functor.map_id, Category.id_comp,
    Homotopy.comp_nullHomotopicMap]

/-- Restriction of the cylinder chain map to the zero endpoint is the first map. -/
@[reassoc]
theorem sheafifiedReducedCylinderChainsMap_zero (H : Homotopy a b) :
    (sheafifiedReducedChains C J).map (cylinderSection X (intervalEndpoint C (1 : Fin 2))) ≫
      sheafifiedReducedCylinderChainsMap X J H = a := by
  have hz : Homotopy.nullHomotopicMap
      (fun i j => (0 : ((sheafifiedReducedChains C J).obj X).X i ⟶ K.X j)) = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    let z : ∀ p q, ((sheafifiedReducedChains C J).obj X).X p ⟶ K.X q := 0
    change dNext i z + prevD i z = 0
    simp only [z, map_zero, add_zero]
  simp only [section_sheafifiedReducedCylinderChainsMap,
    ReducedCylinderChains.normalizedWeight_zero_assoc, zero_comp, hz, add_zero]

/-- Restriction of the cylinder chain map to the one endpoint is the second map. -/
@[reassoc]
theorem sheafifiedReducedCylinderChainsMap_one (H : Homotopy a b) :
    (sheafifiedReducedChains C J).map (cylinderSection X (intervalEndpoint C (0 : Fin 2))) ≫
      sheafifiedReducedCylinderChainsMap X J H = b := by
  simp only [section_sheafifiedReducedCylinderChainsMap,
    ReducedCylinderChains.normalizedWeight_one_assoc]
  exact H.symm.eq_add_nullHomotopicMap.symm

end CategoryTheory.PointedSimplicialPresheaf
