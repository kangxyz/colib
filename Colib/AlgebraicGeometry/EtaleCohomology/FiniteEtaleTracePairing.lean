/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.FiniteEtaleTrace

/-!
# Finite étale trace and natural bilinear pairings

This proves the actual trace identity on sections, not a theorem assuming a
projection formula. A tensor-valued sheaf pairing supplies `b` and `hb`
by precomposing its underlying morphism with the sheaf-to-presheaf tensorator.
The final global tensor-morphism comparison remains to be connected separately.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u
namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Etale.IsSplitOver.finite_I

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g]
variable (F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The split trace projection identity for any natural biadditive sheaf pairing.
The only compatibility assumed is ordinary restriction naturality of that pairing. -/
theorem splitTrace_pairing
    (b : ∀ U : X.Etale, (F.obj.obj (op U)) →+
      (G.obj.obj (op U)) →+ (H.obj.obj (op U)))
    (hb : ∀ {U V : X.Etale} (k : V ⟶ U)
      (a : F.obj.obj (op U)) (c : G.obj.obj (op U)),
      H.obj.map k.op (b U a c) =
        b V (F.obj.map k.op a) (G.obj.map k.op c))
    (U : X.Etale) (h : Stacks.Etale.IsSplitOver g U.hom)
    (a : F.obj.obj (op U)) (c : G.obj.obj (op (baseChangeCompose g U))) :
    splitTrace g H U h rfl
        (b (baseChangeCompose g U) (F.obj.map (baseChangeComposeπ g U).op a) c) =
      b U a (splitTrace g G U h rfl c) := by
  let : Fintype h.I := Fintype.ofFinite _
  rw [splitTrace_apply, splitTrace_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp,
    sheetSection_π, op_id, F.obj.map_id, ConcreteCategory.id_apply]

/-- The existing, globally constructed finite étale trace satisfies the projection
identity on every split object. No auxiliary choice of trace is introduced. -/
theorem finiteEtaleTrace_pairing_on_split [IsFinite g]
    (b : ∀ U : X.Etale, (F.obj.obj (op U)) →+
      (G.obj.obj (op U)) →+ (H.obj.obj (op U)))
    (hb : ∀ {U V : X.Etale} (k : V ⟶ U)
      (a : F.obj.obj (op U)) (c : G.obj.obj (op U)),
      H.obj.map k.op (b U a c) =
        b V (F.obj.map k.op a) (G.obj.map k.op c))
    (U : X.Etale) (h : Stacks.Etale.IsSplitOver g U.hom)
    (a : F.obj.obj (op U)) (c : G.obj.obj (op (baseChangeCompose g U))) :
    (finiteEtaleTrace g H).hom.app (op U)
        (b (baseChangeCompose g U) (F.obj.map (baseChangeComposeπ g U).op a) c) =
      b U a ((finiteEtaleTrace g G).hom.app (op U) c) := by
  rw [finiteEtaleTrace_app g H U h, finiteEtaleTrace_app g G U h]
  exact splitTrace_pairing g F G H b hb U h a c

/-- The actual trace projection identity on all étale objects, by descent from
split objects. This is the sectionwise form of the sheaf-level square. -/
theorem finiteEtaleTrace_pairing [IsFinite g]
    (b : ∀ U : X.Etale, (F.obj.obj (op U)) →+
      (G.obj.obj (op U)) →+ (H.obj.obj (op U)))
    (hb : ∀ {U V : X.Etale} (k : V ⟶ U)
      (a : F.obj.obj (op U)) (c : G.obj.obj (op U)),
      H.obj.map k.op (b U a c) =
        b V (F.obj.map k.op a) (G.obj.map k.op c))
    (U : X.Etale) (a : F.obj.obj (op U))
    (c : G.obj.obj (op (baseChangeCompose g U))) :
    (finiteEtaleTrace g H).hom.app (op U)
        (b (baseChangeCompose g U) (F.obj.map (baseChangeComposeπ g U).op a) c) =
      b U a ((finiteEtaleTrace g G).hom.app (op U) c) := by
  let R : Sieve U :=
    { arrows := fun V _ => Nonempty (Stacks.Etale.IsSplitOver g V.hom)
      downward_closed := by
        intro V W k hk l
        obtain ⟨h⟩ := hk
        exact ⟨(MorphismProperty.Over.w l) ▸ h.comp l.left⟩ }
  have hR : R ∈ X.smallEtaleTopology U := by
    rw [mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨W, e, he, w, hw, ⟨hs⟩⟩ := Stacks.Etale.exists_isSplitOver g U.hom x
    let V : X.Etale := MorphismProperty.Over.mk ⊤ (e ≫ U.hom) (by infer_instance)
    exact ⟨V, MorphismProperty.Over.homMk e rfl, ⟨hs⟩, w, hw⟩
  refine smallEtale_section_ext H R hR _ _ fun V k ⟨h⟩ => ?_
  let k' : baseChangeCompose g V ⟶ baseChangeCompose g U :=
    (Scheme.Etale.smallEtaleCompose g).map ((smallEtaleBaseChange g).map k)
  have htrace (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (z : Q.obj.obj (op (baseChangeCompose g U))) :
      Q.obj.map k.op ((finiteEtaleTrace g Q).hom.app (op U) z) =
        (finiteEtaleTrace g Q).hom.app (op V) (Q.obj.map k'.op z) :=
    (ConcreteCategory.congr_hom ((finiteEtaleTrace g Q).hom.naturality k.op) z).symm
  have hπ : F.obj.map k'.op (F.obj.map (baseChangeComposeπ g U).op a) =
      F.obj.map (baseChangeComposeπ g V).op (F.obj.map k.op a) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun q => F.obj.map q.op a)
      ((Scheme.Etale.smallEtaleComposeBaseChangeAdj g).counit.naturality k)
  rw [htrace, hb, hπ, finiteEtaleTrace_pairing_on_split g F G H b hb V h,
    hb, htrace]

end Stacks.EtaleCohomology
