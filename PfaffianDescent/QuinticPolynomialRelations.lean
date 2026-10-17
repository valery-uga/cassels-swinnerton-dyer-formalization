import PfaffianDescent.QuinticSyzygyMatrix
import PfaffianDescent.HomogeneousProjection

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

/-- The explicit five quadratic equations, as polynomials over the coefficient field. -/
noncomputable def quinticRelations (a : Vec K 5) : Fin 5 → MvPolynomial (Fin 4) K :=
  quinticQuadrics (fun i => C (a i)) X

lemma quinticRelations_eval (a : Vec K 5) (x : Vec K 4) (i : Fin 5) :
    eval₂Hom (RingHom.id K) x (quinticRelations a i) = quinticQuadrics a x i := by
  rw [quinticRelations, quinticQuadrics_map]
  simp only [Function.comp_def, eval₂Hom_C, RingHom.id_apply, eval₂Hom_X']

lemma quinticRelations_homogeneous (a : Vec K 5) (i : Fin 5) :
    (quinticRelations a i).IsHomogeneous 2 := by
  have hx (j : Fin 4) := isHomogeneous_X K j
  have hc (k : Fin 5) (j : Fin 4) := isHomogeneous_C_mul_X (a k) j
  fin_cases i
  · exact ((hx 0).mul (hx 2)).sub ((hx 1).pow 2)
  · exact ((hx 0).mul (hx 3)).sub ((hx 1).mul (hx 2))
  · exact ((hx 1).mul (hx 3)).sub ((hx 2).pow 2)
  · exact ((((((hx 2).mul (hx 3)).add ((hc 4 1).mul (hx 3))).add
      ((hc 3 0).mul (hx 3))).add ((hc 2 0).mul (hx 2))).add
      ((hc 1 0).mul (hx 1))).add (((hx 0).pow 2).C_mul (a 0))
  · exact ((((((hx 3).pow 2).add ((hc 4 2).mul (hx 3))).add
      ((hc 3 1).mul (hx 3))).add ((hc 2 0).mul (hx 3))).add
      ((hc 1 0).mul (hx 2))).add ((hc 0 0).mul (hx 1))

/-- The five explicit quintic quadrics are independent for every choice of coefficients. -/
theorem quinticRelations_independent (a : Vec K 5) :
    LinearIndependent K (quinticRelations a) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he (x : Vec K 4) : (∑ j, c j * quinticQuadrics a x j) = 0 := by
    have h := congrArg (eval₂Hom (RingHom.id K) x) hc
    simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval₂Hom_C,
      RingHom.id_apply, quinticRelations_eval, map_zero] using h
  have h0 : c 0 = 0 := by
    simpa [quinticQuadrics, Fin.sum_univ_succ] using he ![0, 1, 0, 0]
  have h2 : c 2 = 0 := by
    simpa [quinticQuadrics, Fin.sum_univ_succ] using he ![0, 0, 1, 0]
  have h4 : c 4 = 0 := by
    simpa [quinticQuadrics, Fin.sum_univ_succ] using he ![0, 0, 0, 1]
  have h1 : c 1 = 0 := by
    simpa [quinticQuadrics, Fin.sum_univ_succ, h0, h2, h4] using he ![0, 1, 1, 0]
  have h3 : c 3 = 0 := by
    simpa [quinticQuadrics, Fin.sum_univ_succ, h0, h1, h2, h4] using he ![0, 0, 1, 1]
  fin_cases i <;> assumption

end
end PfaffianDescent
