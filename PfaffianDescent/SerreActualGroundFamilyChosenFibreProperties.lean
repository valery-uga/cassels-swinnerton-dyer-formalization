import PfaffianDescent.SerreActualGroundFamilyChosenFibreIso
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! Finiteness and flatness of the actual chosen common fibre transfer to
its literal canonical fibre, preserving the projection to the chosen base. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {S X P Q Z U : Scheme.{u}}
variable (x : X ⟶ S) (p : P ⟶ S) (q : Q ⟶ S)
variable (v : P ⟶ Q) (hv : v ≫ q = p)
variable (n : pullback x p ⟶ pullback x q)
variable (hnX : n ≫ pullback.fst x q = pullback.fst x p)
variable (hnQ : n ≫ pullback.snd x q = pullback.snd x p ≫ v)
variable (z : Z ⟶ pullback x q) (b : U ⟶ P)

@[reassoc]
theorem serreActualGroundFamily_chosenFibreIso_inv_parameter :
    (serreActualGroundFamily_chosenFibreIso x p q v hv n hnX hnQ z b).inv ≫
        pullback.fst b (pullback.fst n z ≫ pullback.snd x p) =
      pullback.snd (z ≫ pullback.snd x q) (b ≫ v) := by
  rw [← serreActualGroundFamily_chosenFibreIso_hom_parameter x p q v hv n hnX hnQ z b,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

include hv hnX hnQ

/-- Only the selected common fibre needs to be finite. -/
theorem serreActualGroundFamily_chosenFibre_isFinite
    [IsFinite (pullback.fst b (pullback.fst n z ≫ pullback.snd x p))] :
    IsFinite (pullback.snd (z ≫ pullback.snd x q) (b ≫ v)) := by
  rw [← serreActualGroundFamily_chosenFibreIso_inv_parameter x p q v hv n hnX hnQ z b]
  infer_instance

theorem serreActualGroundFamily_chosenFibre_flat
    [Flat (pullback.fst b (pullback.fst n z ≫ pullback.snd x p))] :
    Flat (pullback.snd (z ≫ pullback.snd x q) (b ≫ v)) := by
  rw [← serreActualGroundFamily_chosenFibreIso_inv_parameter x p q v hv n hnX hnQ z b]
  infer_instance

end PfaffianDescent
