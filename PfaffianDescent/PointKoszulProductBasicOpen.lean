import PfaffianDescent.PointKoszulStandardInverseCoefficient

/-!
# Actual inverse-product lifts on the product basic open

The parameters become invertible on the actual intersection of their
principal opens. Their inverse sections and the positive inverse-product
Koszul coefficient are constructed from the scheme restriction map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The actual double-principal-open geometry supplies the inverse sections
and their signed Koszul boundary, with no invertibility hypotheses. -/
theorem exists_pointKoszul_product_basicOpen_inverse_boundary
    {X : Scheme.{u}} {U : X.Opens} (q f : Γ(X, U)) :
    let W := X.basicOpen (q * f)
    let j : W ⟶ U := homOfLE (X.basicOpen_le (q * f))
    ∃ uq uf c : Γ(X, W),
      X.presheaf.map j.op q * uq = 1 ∧
      X.presheaf.map j.op f * uf = 1 ∧
      (X.presheaf.map j.op q * X.presheaf.map j.op f) * c = 1 ∧
      uq * uf = c ∧
      sectionRepresenterOverlapScalar X.ringCatSheaf j c ≫
          sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
        0 - sectionRepresenterKoszulOverlapLift X.ringCatSheaf j 0 (-uf) +
          sectionRepresenterKoszulOverlapLift X.ringCatSheaf j (-uq) 0 := by
  dsimp only
  let W := X.basicOpen (q * f)
  let j : W ⟶ U := homOfLE (X.basicOpen_le (q * f))
  let rq := X.presheaf.map j.op q
  let rf := X.presheaf.map j.op f
  have hu : IsUnit (rq * rf) := by
    change IsUnit (X.presheaf.map j.op q * X.presheaf.map j.op f)
    rw [← map_mul]
    exact X.toRingedSpace.isUnit_res_basicOpen (q * f)
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have hq : rq * (rf * c) = 1 := by simpa only [mul_assoc] using hc
  have hf : rf * (rq * c) = 1 := by
    calc
      rf * (rq * c) = (rq * rf) * c := by ring
      _ = 1 := hc
  have hprod : (rf * c) * (rq * c) = c := by
    linear_combination c * hc
  refine ⟨rf * c, rq * c, c, hq, hf, hc, hprod, ?_⟩
  have h := sectionRepresenterKoszul_standard_inverse_boundary j q f (rf * c) (rq * c) hq hf
  rw [hprod] at h
  exact h

end PfaffianDescent
