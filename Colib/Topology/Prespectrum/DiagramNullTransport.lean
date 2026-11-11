/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.DiagramNullHomotopy
public import Colib.Topology.Prespectrum.ConeDiagram
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Coefficient-natural original null tracks and actual isomorphism transport

A diagram null homotopy records the whole original pointwise tracks and their strict
coefficient naturality. Transport through specified original diagram isomorphisms preserves
all times by explicit precomposition and postcomposition. The actual cone descent is conjugated
by the original strict cone isomorphism, with no new choice of null track.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u v w
namespace Topology.LoopPrespectrum
variable {C : Type u} [Category.{v} C]
    {F G K : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (b : G ⟶ K)

namespace DiagramNullHomotopy
variable {a b} (H : DiagramNullHomotopy a b)
    {F' G' K' : C ⥤ LoopPrespectrum.{w}} {a' : F' ⟶ G'} {b' : G' ⟶ K'}
    (eF : F' ≅ F) (eG : G' ≅ G) (eK : K' ≅ K)
    (ha : a' ≫ eG.hom = eF.hom ≫ a) (hb : b' ≫ eK.hom = eG.hom ≫ b)

include ha hb in
private theorem transportedSource :
    eF.hom ≫ (a ≫ b) ≫ eK.inv = a' ≫ b' := by
  calc
    eF.hom ≫ (a ≫ b) ≫ eK.inv = (eF.hom ≫ a) ≫ b ≫ eK.inv := by
      simp only [Category.assoc]
    _ = (a' ≫ eG.hom) ≫ b ≫ eK.inv := by rw [← ha]
    _ = a' ≫ (eG.hom ≫ b) ≫ eK.inv := by simp only [Category.assoc]
    _ = a' ≫ (b' ≫ eK.hom) ≫ eK.inv := by rw [← hb]
    _ = a' ≫ b' := by simp only [Category.assoc, eK.hom_inv_id, Category.comp_id]

/-- Conjugate the same whole null tracks through the specified original diagram isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/DiagramNullHomotopy.lean:54"
  "adaptation" "Original whole-null transport and actual cone isomorphism."]
def transport : DiagramNullHomotopy a' b' where
  homotopy X := (((H.homotopy X).precomp (eF.hom.app X)).postcomp (eK.inv.app X)).cast
    (by
      simpa only [NatTrans.comp_app, Category.assoc] using
        congrArg (fun f ↦ f.app X) (transportedSource eF eG eK ha hb))
    (by
      apply Hom.ext
      funext n
      ext x
      exact (eK.inv.app X).map_point n)
  naturality {X Y} f n r x := by
    change (K'.map f).map n ((eK.inv.app X).map n
      ((H.homotopy X).level n (r, (eF.hom.app X).map n x))) =
      (eK.inv.app Y).map n ((H.homotopy Y).level n
        (r, (eF.hom.app Y).map n ((F'.map f).map n x)))
    rw [← show (eK.inv.app Y).map n
        ((K.map f).map n ((H.homotopy X).level n (r, (eF.hom.app X).map n x))) =
      (K'.map f).map n ((eK.inv.app X).map n
        ((H.homotopy X).level n (r, (eF.hom.app X).map n x))) from
      congrArg (fun g ↦ g.map n ((H.homotopy X).level n (r, (eF.hom.app X).map n x)))
        (eK.inv.naturality f)]
    rw [H.naturality]
    exact congrArg (fun y ↦ (eK.inv.app Y).map n ((H.homotopy Y).level n (r, y)))
      (congrArg (fun g ↦ g.map n x) (eF.hom.naturality f)).symm

/-- Every transported value retains the original time and the specified original point maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/DiagramNullHomotopy.lean:80"
  "adaptation" "Original whole-null transport and actual cone isomorphism."]
theorem transport_level (X : C) (n : ℕ) (r : unitInterval) (x : (F'.obj X).space n) :
    ((H.transport eF eG eK ha hb).homotopy X).level n (r, x) =
      (eK.inv.app X).map n ((H.homotopy X).level n (r, (eF.hom.app X).map n x)) := rfl

/-- The actual strict cone isomorphism of the specified original source square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/DiagramNullHomotopy.lean:85"
  "adaptation" "Original whole-null transport and actual cone isomorphism."]
def coneTransportIso (X : C) : mappingCone (a'.app X) ≅ mappingCone (a.app X) :=
  mappingConeFunctor.mapIso
    (Arrow.isoMk (f := Arrow.mk (a'.app X)) (g := Arrow.mk (a.app X))
      (eF.app X) (eG.app X) (congrArg (fun f ↦ f.app X) ha).symm)

/-- The same original quotient descent is transported by the actual strict cone isomorphism. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/DiagramNullHomotopy.lean:91"
  "adaptation" "Original whole-null transport and actual cone isomorphism."]
theorem transport_coneDesc (X : C) :
    mappingConeDesc (a'.app X) (b'.app X) ((H.transport eF eG eK ha hb).homotopy X) =
      (coneTransportIso eF eG ha X).hom ≫
        mappingConeDesc (a.app X) (b.app X) (H.homotopy X) ≫ eK.inv.app X := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext n
    ext x
    change (b'.app X).map n x =
      ((eG.hom.app X ≫ b.app X) ≫ eK.inv.app X).map n x
    have h := congrArg (fun f ↦ f.app X) hb
    have hi := congrArg (fun f ↦ f.app X) eK.hom_inv_id
    simp only [NatTrans.comp_app, NatTrans.id_app] at h hi
    have hc : (eG.hom.app X ≫ b.app X) ≫ eK.inv.app X = b'.app X := by
      rw [← h, Category.assoc, hi, Category.comp_id]
    exact (congrArg (fun f ↦ f.map n x) hc).symm
  · intro n r x
    rfl

end DiagramNullHomotopy
end Topology.LoopPrespectrum
