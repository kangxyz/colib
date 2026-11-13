/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.Connected
public import Colib.KTheory.Quillen.Map.RebasePath
public import Colib.KTheory.Quillen.Map.NaturalIso
public import Colib.Topology.ClassifyingSpace.UniverseHomotopyTracks
public import Colib.Topology.ClassifyingSpace.ArrowPaths
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportComposition
public import Colib.Topology.Homotopy.HomotopyGroup.Equivalence

/-!
# Original exact K-maps in independent endpoint universes

Every exact functor acts on the original Quillen K-groups by realizing its
actual Q-functor and transporting along the edge of the canonical zero-object
isomorphism. This agrees with the existing strictly rebased KMap whenever the
endpoint universes agree. Actual categorical triangles and natural-transformation
vertex tracks prove composition and natural-isomorphism invariance in every
degree, including K0; no commutativity or untracked basepoint choice is used.

The present consumer compares lower and upper SmallK presentations of the SAME
original category and retains the original affine coherent pushforward square.
It changes no group objects and asserts no identification of categories with
different module-carrier universes. No shared rebasing construction is changed.
-/

/-! Implementation provenance: `Quillen/KTheory/Map/UniverseComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; actual maps and universes are retained. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u₁ v₁ u₂ v₂ u₃ v₃ u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology HomotopyGroup
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactFunctor

private theorem correctedMap_cast {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B))
    {a : A} {b c : B} (h : f a = b) (p : Path b c) (n : ℕ)
    (α : HomotopyGroup.Pi n A a) :
    pathTransport (p.cast h rfl) n (HomotopyGroup.map f rfl α) =
      pathTransport p n (HomotopyGroup.map f h α) := by
  subst b
  rfl

private theorem correctedMap_congr {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] {f g : C(A, B)} (h : f = g)
    {a : A} {b : B} (p : Path (f a) b) (q : Path (g a) b)
    (hpq : ∀ t, p t = q t) (n : ℕ) (α : HomotopyGroup.Pi n A a) :
    pathTransport p n (HomotopyGroup.map f rfl α) =
      pathTransport q n (HomotopyGroup.map g rfl α) := by
  subst g
  have he : p = q := Path.ext (funext hpq)
  subst q
  rfl

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The canonical Q-zero-isomorphism edge, starting at the original cross-universe image point. -/
def universalQZeroBasePath (F : ExactFunctor EC ED) :
    Path (classifyingSpaceMapUniversal F.mapQ EC.kBasepoint) ED.kBasepoint :=
  (classifyingSpacePath (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom).cast
    (classifyingSpaceMapUniversal_point F.mapQ EC.qZero) rfl

/-- The original raw Q-map followed by transport along its canonical zero-isomorphism edge. -/
def universalKMap (F : ExactFunctor EC ED) (n : ℕ) : EC.K n →* ED.K n :=
  (pathTransportMulEquiv (universalQZeroBasePath F) n).toMonoidHom.comp
    (piMap n (classifyingSpaceMapUniversal F.mapQ) rfl)

/-- The corrected map uses the actual zero-isomorphism edge with no endpoint reparametrization. -/
theorem universalKMap_apply (F : ExactFunctor EC ED) (n : ℕ) (a : EC.K n) :
    universalKMap F n a =
      pathTransport (classifyingSpacePath (ED.qIsoOfIso F.toFunctor.mapZeroObject).hom) (n + 1)
        (HomotopyGroup.map (classifyingSpaceMapUniversal F.mapQ)
          (classifyingSpaceMapUniversal_point F.mapQ EC.qZero) a) :=
  correctedMap_cast _ _ _ _ _

/-- A Q-equivalence induces a K-equivalence in arbitrary endpoint universes,
with original map forward. -/
def universalKEquivOfMapQIsEquivalence (F : ExactFunctor EC ED) [F.mapQ.IsEquivalence] (n : ℕ) :
    EC.K n ≃* ED.K n :=
  (homotopyEquivPiEquiv (equivalenceClassifyingHomotopyEquivUniversal F.mapQ.asEquivalence)
    rfl n).trans (pathTransportMulEquiv (universalQZeroBasePath F) n)

/-- The forward equivalence is exactly the canonical cross-universe corrected map. -/
theorem universalKEquivOfMapQIsEquivalence_coe (F : ExactFunctor EC ED)
    [F.mapQ.IsEquivalence] (n : ℕ) :
    (universalKEquivOfMapQIsEquivalence F n).toMonoidHom = universalKMap F n := rfl

private theorem mapQ_qIsoOfIso_universal (F : ExactFunctor EC ED) {X Y : C} (e : X ≅ Y) :
    F.mapQ.mapIso (EC.qIsoOfIso e) = ED.qIsoOfIso (F.toFunctor.mapIso e) := by
  apply Iso.ext
  apply Quotient.sound
  refine ⟨Span.mkIso (Iso.refl _) ?_ ?_⟩
  · change 𝟙 (F.toFunctor.obj X) ≫ 𝟙 (F.toFunctor.obj X) = F.toFunctor.map (𝟙 X)
    simp
  · change 𝟙 (F.toFunctor.obj X) ≫ F.toFunctor.map e.hom = F.toFunctor.map e.hom
    simp

/-- An original natural isomorphism preserves the corrected K-map in every degree,
including zero. -/
theorem universalKMap_eq_of_natIso {F G : ExactFunctor EC ED}
    (e : F.toFunctor ≅ G.toFunctor) (n : ℕ) :
    universalKMap F n = universalKMap G n := by
  let α := ExactFunctor.mapQIso e
  let zF := ED.qIsoOfIso F.toFunctor.mapZeroObject
  let zG := ED.qIsoOfIso G.toFunctor.mapZeroObject
  have he : (α.app EC.qZero).hom ≫ zG.hom = zF.hom := by
    change (ED.qIsoOfIso (e.app (0 : C))).hom ≫
      (ED.qIsoOfIso G.toFunctor.mapZeroObject).hom = _
    rw [← Iso.trans_hom, ← ExactStructure.qIsoOfIso_trans]
    have hz : e.app (0 : C) ≪≫ G.toFunctor.mapZeroObject = F.toFunctor.mapZeroObject := by
      apply Iso.ext
      apply Subsingleton.elim
    exact congrArg (fun t => (ED.qIsoOfIso t).hom) hz
  have hp := classifyingSpacePath_comp (α.app EC.qZero).hom zG.hom
  rw [he] at hp
  ext a
  rw [universalKMap_apply, universalKMap_apply]
  change pathTransport (classifyingSpacePath zF.hom) (n + 1)
      (HomotopyGroup.map (classifyingSpaceMapUniversal F.mapQ)
        (classifyingSpaceMapUniversal_point F.mapQ EC.qZero) a) = _
  exact (congrArg (fun k => k (HomotopyGroup.map (classifyingSpaceMapUniversal F.mapQ)
      (classifyingSpaceMapUniversal_point F.mapQ EC.qZero) a))
        (pathTransport_eq_of_homotopic hp (n + 1))).symm.trans
    ((pathTransport_trans (classifyingSpacePath (α.app EC.qZero).hom)
      (classifyingSpacePath zG.hom) (n + 1) _).trans
        (congrArg (pathTransport (classifyingSpacePath zG.hom) (n + 1))
          (pathTransport_classifyingSpaceMapUniversal_naturalTransformation
            α.hom EC.qZero (n + 1) a)))

section Composition
variable {T : Type u₃} [Category.{v₃} T] [Preadditive T] [HasFiniteBiproducts T]
  {ET : ExactStructure T}

/-- Actual zero-isomorphism triangles prove composition in every K-degree without commutativity. -/
theorem universalKMap_comp (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) (n : ℕ) :
    universalKMap (F.comp G) n = (universalKMap G n).comp (universalKMap F n) := by
  let zF := ED.qIsoOfIso F.toFunctor.mapZeroObject
  let zG := ET.qIsoOfIso G.toFunctor.mapZeroObject
  let zFG := ET.qIsoOfIso (F.comp G).toFunctor.mapZeroObject
  have he : G.mapQ.map zF.hom ≫ zG.hom = zFG.hom := by
    have hq : G.mapQ.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
        ET.qIsoOfIso G.toFunctor.mapZeroObject =
          ET.qIsoOfIso (F.comp G).toFunctor.mapZeroObject := by
      rw [mapQ_qIsoOfIso_universal, ← ExactStructure.qIsoOfIso_trans]
      congr 1
      apply Iso.ext
      apply Subsingleton.elim
    exact congrArg Iso.hom hq
  have hp := classifyingSpacePath_comp (G.mapQ.map zF.hom) zG.hom
  rw [he] at hp
  ext a
  change universalKMap (F.comp G) n a = universalKMap G n (universalKMap F n a)
  rw [universalKMap_apply, universalKMap_apply, universalKMap_apply]
  let b := HomotopyGroup.map (classifyingSpaceMapUniversal F.mapQ)
    (classifyingSpaceMapUniversal_point F.mapQ EC.qZero) a
  have hn := pathTransport_naturality_of_track (classifyingSpaceMapUniversal G.mapQ)
    (classifyingSpacePath zF.hom) (classifyingSpacePath (G.mapQ.map zF.hom))
      (classifyingSpaceMapUniversal_point G.mapQ (F.mapQ.obj EC.qZero))
      (classifyingSpaceMapUniversal_point G.mapQ ED.qZero)
      (fun t => classifyingSpaceMapUniversal_path G.mapQ zF.hom t) (n + 1) b
  have hm : HomotopyGroup.map (classifyingSpaceMapUniversal (F.comp G).mapQ)
      (classifyingSpaceMapUniversal_point (F.comp G).mapQ EC.qZero) a =
    HomotopyGroup.map (classifyingSpaceMapUniversal G.mapQ)
      (classifyingSpaceMapUniversal_point G.mapQ (F.mapQ.obj EC.qZero))
        (HomotopyGroup.map (classifyingSpaceMapUniversal F.mapQ)
          (classifyingSpaceMapUniversal_point F.mapQ EC.qZero) a) := by
    simp only [F.mapQ_comp G, classifyingSpaceMapUniversal_comp]
    exact HomotopyGroup.map_comp _ _ _ _ a
  calc
    pathTransport (classifyingSpacePath zFG.hom) (n + 1) _ =
        pathTransport (classifyingSpacePath zFG.hom) (n + 1)
          (HomotopyGroup.map (classifyingSpaceMapUniversal G.mapQ)
            (classifyingSpaceMapUniversal_point G.mapQ (F.mapQ.obj EC.qZero)) b) :=
      congrArg (pathTransport (classifyingSpacePath zFG.hom) (n + 1)) hm
    _ = pathTransport ((classifyingSpacePath (G.mapQ.map zF.hom)).trans
          (classifyingSpacePath zG.hom)) (n + 1) _ :=
      congrArg (fun k => k (HomotopyGroup.map (classifyingSpaceMapUniversal G.mapQ)
        (classifyingSpaceMapUniversal_point G.mapQ (F.mapQ.obj EC.qZero)) b))
          (pathTransport_eq_of_homotopic hp (n + 1)).symm
    _ = pathTransport (classifyingSpacePath zG.hom) (n + 1)
        (pathTransport (classifyingSpacePath (G.mapQ.map zF.hom)) (n + 1) _) :=
      pathTransport_trans _ _ _ _
    _ = _ := congrArg (pathTransport (classifyingSpacePath zG.hom) (n + 1)) hn
end Composition

section Common
variable {A B : Type u} [Category.{v} A] [Category.{v} B]
  [Preadditive A] [HasFiniteBiproducts A] [Preadditive B] [HasFiniteBiproducts B]
  {EA : ExactStructure A} {EB : ExactStructure B}

/-- In common endpoint universes, the corrected map equals the repository's original KMap. -/
theorem universalKMap_eq_KMap (F : ExactFunctor EA EB) (n : ℕ) :
    universalKMap F n = F.KMap n := by
  ext a
  change pathTransport (universalQZeroBasePath F) (n + 1)
    (HomotopyGroup.map (classifyingSpaceMapUniversal F.mapQ) rfl a) = F.KMap n a
  have h := DFunLike.congr_fun (F.KMap_eq_pathTransport n) a
  change F.KMap n a = pathTransport F.qZeroBasePath (n + 1)
    (HomotopyGroup.map (classifyingSpaceMap F.mapQ).hom rfl a) at h
  rw [h]
  exact correctedMap_congr (classifyingSpaceMapUniversal_eq F.mapQ)
    (universalQZeroBasePath F) F.qZeroBasePath (fun _ => rfl) (n + 1) a
end Common

end CategoryTheory.ExactCategory.ExactFunctor
