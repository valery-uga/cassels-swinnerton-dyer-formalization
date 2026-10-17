import Mathlib.AlgebraicGeometry.Limits

/-! Exact selected fibres of an actual surface--parameter family. -/
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

/-- The canonical selected fibre maps to the actual common-family fibre. -/
def serreActualGroundFamily_chosenFibreFromCanonical :
    pullback (z ≫ pullback.snd x q) (b ≫ v) ⟶
      pullback b (pullback.fst n z ≫ pullback.snd x p) := by
  let a := pullback.fst (z ≫ pullback.snd x q) (b ≫ v)
  let c := pullback.snd (z ≫ pullback.snd x q) (b ≫ v)
  have hbase : (a ≫ z ≫ pullback.fst x q) ≫ x = (c ≫ b) ≫ p := by
    calc
      _ = (a ≫ (z ≫ pullback.snd x q)) ≫ q := by
        simp only [Category.assoc, pullback.condition]
      _ = (c ≫ (b ≫ v)) ≫ q :=
        congrArg (fun f => f ≫ q)
          (pullback.condition (f := z ≫ pullback.snd x q) (g := b ≫ v))
      _ = _ := by simp only [Category.assoc, hv]
  let t : pullback (z ≫ pullback.snd x q) (b ≫ v) ⟶ pullback x p :=
    pullback.lift (a ≫ z ≫ pullback.fst x q) (c ≫ b) hbase
  have hzero : t ≫ n = a ≫ z := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hnX, t, pullback.lift_fst]
    · simp only [Category.assoc, hnQ, t, pullback.lift_snd_assoc]
      simpa only [Category.assoc] using
        (pullback.condition (f := z ≫ pullback.snd x q) (g := b ≫ v)).symm
  let w : pullback (z ≫ pullback.snd x q) (b ≫ v) ⟶ pullback n z :=
    pullback.lift t a hzero
  exact pullback.lift c w (by
    simp only [w, Category.assoc, pullback.lift_fst_assoc, t, pullback.lift_snd])

/-- The common-family selected fibre maps to the literal canonical zero fibre
at the same chosen parameter, with no comparison supplied as a premise. -/
def serreActualGroundFamily_chosenFibreToCanonical :
    pullback b (pullback.fst n z ≫ pullback.snd x p) ⟶
      pullback (z ≫ pullback.snd x q) (b ≫ v) := by
  let c := pullback.fst b (pullback.fst n z ≫ pullback.snd x p)
  let w := pullback.snd b (pullback.fst n z ≫ pullback.snd x p)
  refine pullback.lift (w ≫ pullback.snd n z) c ?_
  calc
    (w ≫ pullback.snd n z) ≫ (z ≫ pullback.snd x q) =
        w ≫ pullback.fst n z ≫ n ≫ pullback.snd x q := by
      rw [Category.assoc, ← pullback.condition_assoc]
    _ = w ≫ pullback.fst n z ≫ pullback.snd x p ≫ v := by rw [hnQ]
    _ = c ≫ b ≫ v := by
      simpa only [Category.assoc] using (congrArg (fun f => f ≫ v)
        (pullback.condition (f := b) (g := pullback.fst n z ≫ pullback.snd x p))).symm

/-- Both fibre descriptions are the same actual pullback, including its
surface projection and selected parameter. -/
def serreActualGroundFamily_chosenFibreIso :
    pullback b (pullback.fst n z ≫ pullback.snd x p) ≅
      pullback (z ≫ pullback.snd x q) (b ≫ v) where
  hom := serreActualGroundFamily_chosenFibreToCanonical x p q v n hnQ z b
  inv := serreActualGroundFamily_chosenFibreFromCanonical x p q v hv n hnX hnQ z b
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [serreActualGroundFamily_chosenFibreToCanonical,
        serreActualGroundFamily_chosenFibreFromCanonical, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [serreActualGroundFamily_chosenFibreToCanonical,
            serreActualGroundFamily_chosenFibreFromCanonical, Category.assoc,
            pullback.lift_snd_assoc, pullback.lift_fst_assoc, pullback.lift_fst,
            Category.id_comp]
          rw [← pullback.condition_assoc, hnX]
        · simp only [serreActualGroundFamily_chosenFibreToCanonical,
            serreActualGroundFamily_chosenFibreFromCanonical, Category.assoc,
            pullback.lift_snd_assoc, pullback.lift_fst_assoc, pullback.lift_snd,
            pullback.lift_fst, Category.id_comp]
          simpa only [Category.assoc] using
            (pullback.condition (f := b) (g := pullback.fst n z ≫ pullback.snd x p))
      · simp only [serreActualGroundFamily_chosenFibreToCanonical,
          serreActualGroundFamily_chosenFibreFromCanonical, Category.assoc,
          pullback.lift_snd_assoc, pullback.lift_snd, pullback.lift_fst,
          Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [serreActualGroundFamily_chosenFibreToCanonical,
        serreActualGroundFamily_chosenFibreFromCanonical, Category.assoc,
        pullback.lift_snd_assoc, pullback.lift_snd, pullback.lift_fst,
        Category.id_comp]

@[reassoc]
theorem serreActualGroundFamily_chosenFibreIso_hom_parameter :
    (serreActualGroundFamily_chosenFibreIso x p q v hv n hnX hnQ z b).hom ≫
      pullback.snd (z ≫ pullback.snd x q) (b ≫ v) =
    pullback.fst b (pullback.fst n z ≫ pullback.snd x p) := by
  simp only [serreActualGroundFamily_chosenFibreIso,
    serreActualGroundFamily_chosenFibreToCanonical, pullback.lift_snd]

@[reassoc]
theorem serreActualGroundFamily_chosenFibreIso_hom_surface :
    (serreActualGroundFamily_chosenFibreIso x p q v hv n hnX hnQ z b).hom ≫
      pullback.fst (z ≫ pullback.snd x q) (b ≫ v) ≫ z ≫ pullback.fst x q =
    pullback.snd b (pullback.fst n z ≫ pullback.snd x p) ≫
      pullback.fst n z ≫ pullback.fst x p := by
  simp only [serreActualGroundFamily_chosenFibreIso,
    serreActualGroundFamily_chosenFibreToCanonical, pullback.lift_fst_assoc,
    Category.assoc]
  rw [← pullback.condition_assoc, hnX]

end PfaffianDescent
