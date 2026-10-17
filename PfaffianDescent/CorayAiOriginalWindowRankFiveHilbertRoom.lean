import PfaffianDescent.CorayCubicPolynomialDualAnnihilatorDimension

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original A(i) freedom at least3 and coprime degree actually leave at
least five vector-space dimensions. This is the original numerical window,
not an additional pencil/rank premise. -/
theorem coray_case_Ai_originalWindow_rankFive_hilbertRoom001
    (n d : ℕ) (hn : 2 ≤ n) (hcop : Nat.Coprime d 3)
    (hfreedom : 3 ≤ 3 * (n + 1).choose 2 - d) :
    d + 5 ≤ (n + 3).choose 3 - n.choose 3 := by
  have hchoose : (n + 3).choose 3 - n.choose 3 = 1 + 3 * (n + 1).choose 2 := by
    by_cases hn3 : 3 ≤ n
    · have h := cubicPolynomialAnnihilator_choose_difference (n + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel] using h
    · have he : n = 2 := by omega
      subst n
      decide
  have hnotdvd : ¬ 3 ∣ d := (Nat.prime_three.coprime_iff_not_dvd.mp hcop.symm)
  have hmod : d % 3 ≠ 0 := by
    intro h
    exact hnotdvd (Nat.dvd_of_mod_eq_zero h)
  rw [hchoose]
  omega

end PfaffianDescent.Coray
