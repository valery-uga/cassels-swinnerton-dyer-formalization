import Mathlib.AlgebraicGeometry.Limits

/-! Exact old selected fibres after a genuine Cartesian surface coefficient change. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

variable {S R X Y P Q Z U : Scheme.{u}}
variable (x : X ⟶ S) (y : Y ⟶ R) (p : P ⟶ R) (q : Q ⟶ S)
variable (k : R ⟶ S) (f : Y ⟶ X) (hY : IsPullback f y x k)
variable (v : P ⟶ Q) (hv : v ≫ q = p ≫ k)
variable (n : pullback y p ⟶ pullback x q)
variable (hnX : n ≫ pullback.fst x q = pullback.fst y p ≫ f)
variable (hnQ : n ≫ pullback.snd x q = pullback.snd y p ≫ v)
variable (z : Z ⟶ pullback x q) (b : U ⟶ P)

/-- The canonical selected fibre maps to the actual common-family fibre. -/
def serreActualGroundFamily_coefficientChosenFibreFromCanonical :
    pullback (z ≫ pullback.snd x q) (b ≫ v) ⟶
      pullback b (pullback.fst n z ≫ pullback.snd y p) := by
  let a := pullback.fst (z ≫ pullback.snd x q) (b ≫ v)
  let c := pullback.snd (z ≫ pullback.snd x q) (b ≫ v)
  have hbaseX : (a ≫ z ≫ pullback.fst x q) ≫ x = (c ≫ b ≫ p) ≫ k := by
    calc
      _ = (a ≫ (z ≫ pullback.snd x q)) ≫ q := by
        simp only [Category.assoc, pullback.condition]
      _ = (c ≫ (b ≫ v)) ≫ q :=
        congrArg (fun u => u ≫ q)
          (pullback.condition (f := z ≫ pullback.snd x q) (g := b ≫ v))
      _ = _ := by simp only [Category.assoc, hv]
  let r : pullback (z ≫ pullback.snd x q) (b ≫ v) ⟶ Y :=
    hY.lift (a ≫ z ≫ pullback.fst x q) (c ≫ b ≫ p) hbaseX
  have hbase : r ≫ y = (c ≫ b) ≫ p := by
    simpa only [Category.assoc] using
      hY.lift_snd (a ≫ z ≫ pullback.fst x q) (c ≫ b ≫ p) hbaseX
  let t : pullback (z ≫ pullback.snd x q) (b ≫ v) ⟶ pullback y p :=
    pullback.lift r (c ≫ b) hbase
  have hzero : t ≫ n = a ≫ z := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hnX, t, pullback.lift_fst_assoc,
        r, IsPullback.lift_fst]
    · simp only [Category.assoc, hnQ, t, pullback.lift_snd_assoc]
      simpa only [Category.assoc] using
        (pullback.condition (f := z ≫ pullback.snd x q) (g := b ≫ v)).symm
  let w : pullback (z ≫ pullback.snd x q) (b ≫ v) ⟶ pullback n z :=
    pullback.lift t a hzero
  exact pullback.lift c w (by
    simp only [w, Category.assoc, pullback.lift_fst_assoc, t, pullback.lift_snd])

/-- The common-family selected fibre maps to the literal canonical zero fibre
at the same chosen parameter, with no comparison supplied as a premise. -/
def serreActualGroundFamily_coefficientChosenFibreToCanonical :
    pullback b (pullback.fst n z ≫ pullback.snd y p) ⟶
      pullback (z ≫ pullback.snd x q) (b ≫ v) := by
  let c := pullback.fst b (pullback.fst n z ≫ pullback.snd y p)
  let w := pullback.snd b (pullback.fst n z ≫ pullback.snd y p)
  refine pullback.lift (w ≫ pullback.snd n z) c ?_
  calc
    (w ≫ pullback.snd n z) ≫ (z ≫ pullback.snd x q) =
        w ≫ pullback.fst n z ≫ n ≫ pullback.snd x q := by
      rw [Category.assoc, ← pullback.condition_assoc]
    _ = w ≫ pullback.fst n z ≫ pullback.snd y p ≫ v := by rw [hnQ]
    _ = c ≫ b ≫ v := by
      simpa only [Category.assoc] using (congrArg (fun f => f ≫ v)
        (pullback.condition (f := b) (g := pullback.fst n z ≫ pullback.snd y p))).symm

/-- Both fibre descriptions are the same actual pullback, including its
surface projection and selected parameter. -/
def serreActualGroundFamily_coefficientChosenFibreIso :
    pullback b (pullback.fst n z ≫ pullback.snd y p) ≅
      pullback (z ≫ pullback.snd x q) (b ≫ v) where
  hom := serreActualGroundFamily_coefficientChosenFibreToCanonical x y p q v n hnQ z b
  inv := serreActualGroundFamily_coefficientChosenFibreFromCanonical x y p q k f hY v hv n hnX hnQ z b
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [serreActualGroundFamily_coefficientChosenFibreToCanonical,
        serreActualGroundFamily_coefficientChosenFibreFromCanonical, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · apply hY.hom_ext
          · simp only [serreActualGroundFamily_coefficientChosenFibreToCanonical,
              serreActualGroundFamily_coefficientChosenFibreFromCanonical, Category.assoc,
              pullback.lift_snd_assoc, pullback.lift_fst_assoc, pullback.lift_fst,
              IsPullback.lift_fst, Category.id_comp]
            rw [← pullback.condition_assoc, hnX]
          · simp only [serreActualGroundFamily_coefficientChosenFibreToCanonical,
              serreActualGroundFamily_coefficientChosenFibreFromCanonical, Category.assoc,
              pullback.lift_snd_assoc, pullback.lift_fst_assoc, pullback.lift_fst,
              IsPullback.lift_snd, Category.id_comp]
            rw [pullback.condition_assoc]
            simp only [Category.assoc]
            rw [pullback.condition]
        · simp only [serreActualGroundFamily_coefficientChosenFibreToCanonical,
            serreActualGroundFamily_coefficientChosenFibreFromCanonical, Category.assoc,
            pullback.lift_snd_assoc, pullback.lift_fst_assoc, pullback.lift_snd,
            pullback.lift_fst, Category.id_comp]
          simpa only [Category.assoc] using
            (pullback.condition (f := b) (g := pullback.fst n z ≫ pullback.snd y p))
      · simp only [serreActualGroundFamily_coefficientChosenFibreToCanonical,
          serreActualGroundFamily_coefficientChosenFibreFromCanonical, Category.assoc,
          pullback.lift_snd_assoc, pullback.lift_snd, pullback.lift_fst,
          Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [serreActualGroundFamily_coefficientChosenFibreToCanonical,
        serreActualGroundFamily_coefficientChosenFibreFromCanonical, Category.assoc,
        pullback.lift_snd_assoc, pullback.lift_snd, pullback.lift_fst,
        Category.id_comp]

@[reassoc]
theorem serreActualGroundFamily_coefficientChosenFibreIso_hom_parameter :
    (serreActualGroundFamily_coefficientChosenFibreIso x y p q k f hY v hv n hnX hnQ z b).hom ≫
      pullback.snd (z ≫ pullback.snd x q) (b ≫ v) =
    pullback.fst b (pullback.fst n z ≫ pullback.snd y p) := by
  simp only [serreActualGroundFamily_coefficientChosenFibreIso,
    serreActualGroundFamily_coefficientChosenFibreToCanonical, pullback.lift_snd]

@[reassoc]
theorem serreActualGroundFamily_coefficientChosenFibreIso_hom_surface :
    (serreActualGroundFamily_coefficientChosenFibreIso x y p q k f hY v hv n hnX hnQ z b).hom ≫
      pullback.fst (z ≫ pullback.snd x q) (b ≫ v) ≫ z ≫ pullback.fst x q =
    pullback.snd b (pullback.fst n z ≫ pullback.snd y p) ≫
      pullback.fst n z ≫ pullback.fst y p ≫ f := by
  simp only [serreActualGroundFamily_coefficientChosenFibreIso,
    serreActualGroundFamily_coefficientChosenFibreToCanonical, pullback.lift_fst_assoc,
    Category.assoc]
  rw [← pullback.condition_assoc, hnX]

@[reassoc]
theorem serreActualGroundFamily_coefficientChosenFibreIso_inv_surface :
    (serreActualGroundFamily_coefficientChosenFibreIso x y p q k f hY v hv n hnX hnQ z b).inv ≫
      pullback.snd b (pullback.fst n z ≫ pullback.snd y p) ≫
        pullback.fst n z ≫ pullback.fst y p ≫ f =
    pullback.fst (z ≫ pullback.snd x q) (b ≫ v) ≫ z ≫ pullback.fst x q := by
  rw [← serreActualGroundFamily_coefficientChosenFibreIso_hom_surface
      x y p q k f hY v hv n hnX hnQ z b,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end PfaffianDescent
