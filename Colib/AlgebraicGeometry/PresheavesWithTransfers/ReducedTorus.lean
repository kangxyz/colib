/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Cokernels
public import Colib.AlgebraicGeometry.Sites.Smooth.Torus

/-!
# Reduced native transfer torus presheaves

Adapted from motivic_source_a6805c4, Transfers/Presheaf/ReducedTorus.lean.
The torus is the existing Stacks native base change; its actual identity
sections and literal relative products were constructed in Smooth.Torus.
Relations are genuine graph cycles. The quotient retains all signed transfers.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k]

/-- The actual transfer representable of the relative `q`-fold torus. -/
def torusRepresentable (q : ℕ) : PresheafWithTransfers.{u + 1} k :=
  (representableLarge k).obj (Cor.mk (SmoothSite.torusPower (Spec (.of k)) q))

/-- All identity-coordinate inclusions, acting by their genuine graph cycles.
There are exactly `q` such maps in weight `q`, and none in weight zero. -/
def torusIdentityAxis : (q : ℕ) → Fin q →
    (torusRepresentable k (q - 1) ⟶ torusRepresentable k q)
  | 0, i => Fin.elim0 i
  | q + 1, i => (representableLarge k).map
      ((Cor.graphFunctor k).map (SmoothSite.torusInsertOne (Spec (.of k)) q i))

/-- An identity axis is literally postcomposition with the actual graph cycle. -/
theorem torusIdentityAxis_app_apply (q : ℕ) (i : Fin (q + 1)) (X : Cor k)
    (α : X ⟶ Cor.mk (SmoothSite.torusPower (Spec (.of k)) q)) :
    (torusIdentityAxis k (q + 1) i).hom.app (op X) (ULift.up α) =
      ULift.up (α ≫ (Cor.graphFunctor k).map
        (SmoothSite.torusInsertOne (Spec (.of k)) q i)) := rfl

instance torus_hasBiproduct (q : ℕ) :
    HasBiproduct (fun _ : Fin q => (torusRepresentable k (q - 1)).obj) :=
  HasBiproduct.of_hasCoproduct _

/-- The finite direct sum of all identity-coordinate relations. -/
def torusRelation (q : ℕ) :
    (⨁ fun _ : Fin q => (torusRepresentable k (q - 1)).obj) ⟶
      (torusRepresentable k q).obj :=
  biproduct.desc (fun i => (torusIdentityAxis k q i).hom)

/-- `ℤ_tr(𝔾ₘ^∧q)` is the quotient of the actual torus representable by the
sum of the images of all genuine identity-coordinate inclusions. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/ReducedTorus.lean:119-120"
  "adaptation" "Actual signed-transfer quotient by all native identity axes"]
def reducedTorus (q : ℕ) : PresheafWithTransfers.{u + 1} k :=
  ⟨cokernel (torusRelation k q), Functor.cokernel_additive (torusRelation k q)⟩

/-- The quotient map from the genuine torus representable. -/
def toReducedTorus (q : ℕ) : torusRepresentable k q ⟶ reducedTorus k q :=
  ⟨cokernel.π (torusRelation k q)⟩

/-- Every identity-coordinate inclusion is killed by the quotient. -/
@[reassoc (attr := simp)]
theorem torusIdentityAxis_toReducedTorus (q : ℕ) (i : Fin q) :
    torusIdentityAxis k q i ≫ toReducedTorus k q = 0 := by
  apply ObjectProperty.hom_ext
  change (torusIdentityAxis k q i).hom ≫ cokernel.π (torusRelation k q) = 0
  calc
    _ = (biproduct.ι _ i ≫ torusRelation k q) ≫
        cokernel.π (torusRelation k q) := by rw [torusRelation, biproduct.ι_desc]
    _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]

/-- The quotient is natural for every signed finite correspondence. -/
@[reassoc]
theorem toReducedTorus_naturality (q : ℕ) {X Y : Cor k} (α : X ⟶ Y) :
    transfer (torusRepresentable k q) α ≫ (toReducedTorus k q).hom.app (op X) =
      (toReducedTorus k q).hom.app (op Y) ≫ transfer (reducedTorus k q) α :=
  transfer_naturality (toReducedTorus k q) α

/-- Transfer of a represented quotient section is the quotient of the literal
incidence-Tor composite, for arbitrary signed correspondences. -/
theorem reducedTorus_transfer_apply (q : ℕ) {X Y : Cor k} (α : X ⟶ Y)
    (β : Y ⟶ Cor.mk (SmoothSite.torusPower (Spec (.of k)) q)) :
    transfer (reducedTorus k q) α ((toReducedTorus k q).hom.app (op Y) (ULift.up β)) =
      (toReducedTorus k q).hom.app (op X) (ULift.up (α ≫ β)) :=
  (NatTrans.naturality_apply (toReducedTorus k q).hom α.op (ULift.up β)).symm

/-- Every reduced section is represented by an actual signed finite cycle. -/
theorem toReducedTorus_surjective (q : ℕ) (X : Cor k) :
    Function.Surjective ((toReducedTorus k q).hom.app (op X)) := by
  change Function.Surjective ((cokernel.π (torusRelation k q)).app (op X))
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  change Epi (((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)).map
    (cokernel.π (torusRelation k q)))
  infer_instance

/-- The subgroup generated by the images of all actual identity axes.
In an abelian group this supremum is precisely their sum. -/
def torusIdentityRelations (q : ℕ) (X : Cor k) :
    AddSubgroup (sections (torusRepresentable k q) X) :=
  ⨆ i : Fin q, ((torusIdentityAxis k q i).hom.app (op X)).hom.range

theorem torus_hom_sum_apply {G H : AddCommGrpCat.{u + 1}} {ι : Type}
    (s : Finset ι) (f : ι → (G ⟶ H)) (x : G) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, AddCommGrpCat.hom_add_apply, ih]

/-- The defining relation morphism is literally the sum of the axis maps. -/
theorem torusRelation_app_apply (q : ℕ) (X : Cor k)
    (s : (⨁ fun _ : Fin q => (torusRepresentable k (q - 1)).obj).obj (op X)) :
    (torusRelation k q).app (op X) s =
      ∑ i : Fin q, (torusIdentityAxis k q i).hom.app (op X)
        ((biproduct.π (fun _ : Fin q => (torusRepresentable k (q - 1)).obj) i).app
          (op X) s) := by
  rw [torusRelation, biproduct.desc_eq, NatTrans.app_sum, torus_hom_sum_apply]
  rfl

/-- The image of the relation map is exactly the sum of the genuine axis images. -/
theorem range_torusRelation (q : ℕ) (X : Cor k) :
    ((torusRelation k q).app (op X)).hom.range = torusIdentityRelations k q X := by
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    rw [torusRelation_app_apply]
    apply AddSubgroup.sum_mem
    intro i _
    exact AddSubgroup.mem_iSup_of_mem i ⟨_, rfl⟩
  · apply iSup_le
    intro i s hs
    obtain ⟨t, rfl⟩ := hs
    refine ⟨(biproduct.ι (fun _ : Fin q => (torusRepresentable k (q - 1)).obj) i).app
      (op X) t, ?_⟩
    exact congrArg (fun f => f.app (op X) t)
      (biproduct.ι_desc (fun j => (torusIdentityAxis k q j).hom) i)

/-- Objectwise, the construction is the actual group quotient by the sum of
the identity-coordinate images, rather than an arbitrary relation object. -/
def reducedTorusSectionsIsoQuotient (q : ℕ) (X : Cor k) :
    sections (reducedTorus k q) X ≅
      AddCommGrpCat.of
        (sections (torusRepresentable k q) X ⧸ torusIdentityRelations k q X) :=
  PreservesCokernel.iso
      ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)) (torusRelation k q) ≪≫
    AddCommGrpCat.cokernelIsoQuotient ((torusRelation k q).app (op X)) ≪≫
    eqToIso (by rw [range_torusRelation])

/-- Extend a transfer-natural map that kills each actual identity axis. -/
def reducedTorusDesc (q : ℕ) {P : PresheafWithTransfers.{u + 1} k}
    (η : torusRepresentable k q ⟶ P)
    (hη : ∀ i : Fin q, torusIdentityAxis k q i ≫ η = 0) :
    reducedTorus k q ⟶ P :=
  ⟨cokernel.desc (torusRelation k q) η.hom (by
    apply biproduct.hom_ext'
    intro i
    have h := congrArg (fun f => f.hom) (hη i)
    change (torusIdentityAxis k q i).hom ≫ η.hom = 0 at h
    simpa only [torusRelation, biproduct.ι_desc_assoc, comp_zero] using h)⟩

/-- The descended map extends the original map along the quotient. -/
@[reassoc (attr := simp)]
theorem toReducedTorus_desc (q : ℕ) {P : PresheafWithTransfers.{u + 1} k}
    (η : torusRepresentable k q ⟶ P)
    (hη : ∀ i : Fin q, torusIdentityAxis k q i ≫ η = 0) :
    toReducedTorus k q ≫ reducedTorusDesc k q η hη = η := by
  apply ObjectProperty.hom_ext
  exact cokernel.π_desc _ _ _

/-- Uniqueness is among maps natural for all signed transfers. -/
theorem reducedTorus_hom_ext (q : ℕ) {P : PresheafWithTransfers.{u + 1} k}
    {η θ : reducedTorus k q ⟶ P}
    (h : toReducedTorus k q ≫ η = toReducedTorus k q ≫ θ) : η = θ := by
  apply ObjectProperty.hom_ext
  apply (cancel_epi (cokernel.π (torusRelation k q))).mp
  exact congrArg (fun f => f.hom) h

/-- The universal property of the quotient, inside transfer presheaves. -/
def reducedTorusHomEquiv (q : ℕ) (P : PresheafWithTransfers.{u + 1} k) :
    (reducedTorus k q ⟶ P) ≃
      {η : torusRepresentable k q ⟶ P //
        ∀ i : Fin q, torusIdentityAxis k q i ≫ η = 0} where
  toFun η := ⟨toReducedTorus k q ≫ η, fun i => by
    rw [← Category.assoc, torusIdentityAxis_toReducedTorus, zero_comp]⟩
  invFun η := reducedTorusDesc k q η.val η.property
  left_inv η := by
    apply reducedTorus_hom_ext
    exact toReducedTorus_desc k q _ _
  right_inv η := by
    apply Subtype.ext
    exact toReducedTorus_desc k q _ _

/-- Weight zero has no identity-axis relations and is the actual representable
of the base scheme. -/
def reducedTorusZeroIso : reducedTorus k 0 ≅
    (representableLarge k).obj (Cor.mk (SmoothSite.base (Spec (.of k)))) where
  hom := reducedTorusDesc k 0 (𝟙 _) (fun i => Fin.elim0 i)
  inv := toReducedTorus k 0
  hom_inv_id := by
    change reducedTorusDesc k 0 (𝟙 (torusRepresentable k 0)) _ ≫
      toReducedTorus k 0 = 𝟙 (reducedTorus k 0)
    apply reducedTorus_hom_ext
    rw [← Category.assoc, toReducedTorus_desc, Category.id_comp, Category.comp_id]
  inv_hom_id := toReducedTorus_desc k 0 _ _

/-- The first torus-power representable is canonically the representable of
the Laurent spectrum itself. -/
def torusRepresentableOneIso : torusRepresentable k 1 ≅
    (representableLarge k).obj (Cor.mk (SmoothSite.multiplicativeGroupObject (Spec (.of k)))) :=
  (representableLarge k).mapIso
    ((Cor.graphFunctor k).mapIso (SmoothSite.torusPowerOneIso (Spec (.of k))))

/-- The actual base-point map of the Laurent spectrum, on transfer representables. -/
def torusOneRepresentable :
    (representableLarge k).obj (Cor.mk (SmoothSite.base (Spec (.of k)))) ⟶
      (representableLarge k).obj (Cor.mk (SmoothSite.multiplicativeGroupObject (Spec (.of k)))) :=
  (representableLarge k).map ((Cor.graphFunctor k).map (SmoothSite.torusOne (Spec (.of k))))

/-- The unique weight-one relation is the genuine Laurent unit section. -/
@[reassoc (attr := simp)]
theorem torusIdentityAxis_one :
    torusIdentityAxis k 1 0 ≫ (torusRepresentableOneIso k).hom =
      torusOneRepresentable k := by
  change (representableLarge k).map
      ((Cor.graphFunctor k).map (SmoothSite.torusInsertOne (Spec (.of k)) 0 0)) ≫
    (representableLarge k).map
      ((Cor.graphFunctor k).map (SmoothSite.torusPowerOneIso (Spec (.of k))).hom) =
    (representableLarge k).map ((Cor.graphFunctor k).map (SmoothSite.torusOne (Spec (.of k))))
  rw [← Functor.map_comp, ← Functor.map_comp, SmoothSite.torusInsertOne_zero_powerOneIso]

/-- The ordinary cokernel of the actual base-point graph, re-bundled with all
signed transfers. This is the familiar pointed Laurent torus presentation. -/
def pointedTorusCokernel : PresheafWithTransfers.{u + 1} k :=
  ⟨cokernel (torusOneRepresentable k).hom,
    Functor.cokernel_additive (torusOneRepresentable k).hom⟩

/-- Weight one is the actual cokernel of `ℤ_tr(Spec k) → ℤ_tr(𝔾ₘ)`
induced by the Laurent identity point. -/
def reducedTorusOneIso : reducedTorus k 1 ≅ pointedTorusCokernel k := by
  let p : (⨁ fun _ : Fin 1 => (torusRepresentable k 0).obj) ≅
      (torusRepresentable k 0).obj :=
    { hom := biproduct.π _ 0
      inv := biproduct.ι (fun _ : Fin 1 => (torusRepresentable k 0).obj) 0
      hom_inv_id := by simpa only [Fin.sum_univ_one] using
        biproduct.total (f := fun _ : Fin 1 => (torusRepresentable k 0).obj)
      inv_hom_id := biproduct.ι_π_self
        (fun _ : Fin 1 => (torusRepresentable k 0).obj) 0 }
  apply ObjectProperty.isoMk
  apply cokernel.mapIso (torusRelation k 1) (torusOneRepresentable k).hom p
    (forget.mapIso (torusRepresentableOneIso k))
  apply biproduct.hom_ext'
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [torusRelation, p, ← Category.assoc, biproduct.ι_desc,
    biproduct.ι_π_self, Category.id_comp]
  have h := congrArg (fun f => f.hom) (torusIdentityAxis_one k)
  change (torusIdentityAxis k 1 0).hom ≫ (torusRepresentableOneIso k).hom.hom =
    (torusOneRepresentable k).hom at h
  exact h

attribute [colib_tag "COL-0385"]
  reducedTorus
  reducedTorusSectionsIsoQuotient
  reducedTorus_transfer_apply
  reducedTorusHomEquiv
  reducedTorusZeroIso

attribute [colib_ref "MVW2006"
  "Lecture 2, Definition 2.12, pp. 15-16"
  "adaptation" "Reduced representable quotient, before applying the singular complex"]
  reducedTorus

end AlgebraicGeometry.PresheafWithTransfers
