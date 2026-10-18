import AllCharacteristics.KollarResidualBaseChange

/-! Arbitrary roots and their actual generic-line centers
under the explicit root-field coefficient map. This covers both chosen and
conjugate residual roots without identifying the target conjugation. -/

noncomputable section
namespace AllCharacteristics
open PfaffianDescent Polynomial
universe u

def kollarResidualLinePoint
    {k : Type u} [Field k] (c : Cubic k 4)
    (r : AdjoinRoot (kollarGenericResidualPolynomial c)) :
    Fin 4 → AdjoinRoot (kollarGenericResidualPolynomial c) :=
  (fun i => AdjoinRoot.of (kollarGenericResidualPolynomial c)
    (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)) (kollarBasePoint k i))) +
    r • (fun i => AdjoinRoot.of (kollarGenericResidualPolynomial c)
      (kollarGenericProjectiveLineDirection k i))

theorem adjoinRootCoefficientMap_eval_root
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Polynomial R) (q : Polynomial S)
    (hpq : p.map f = q) (r : AdjoinRoot p)
    (hr : Polynomial.aeval r p = 0) :
    Polynomial.aeval (adjoinRootCoefficientMap f p q hpq r) q = 0 := by
  let B := adjoinRootCoefficientMap f p q hpq
  have h := congrArg B hr
  simp only [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at h
  change Polynomial.eval₂ (B.comp (AdjoinRoot.of p)) (B r) p = 0 at h
  rw [adjoinRootCoefficientMap_comp_of] at h
  rw [← Polynomial.eval₂_map, hpq] at h
  exact h

theorem kollarResidualRootBaseChange_eval_root
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4)
    (r : AdjoinRoot (kollarGenericResidualPolynomial c))
    (hr : Polynomial.aeval r (kollarGenericResidualPolynomial c) = 0) :
    Polynomial.aeval (kollarResidualRootBaseChange f c r)
      (kollarGenericResidualPolynomial (c.map f)) = 0 := by
  exact adjoinRootCoefficientMap_eval_root _ _ _
    (kollarGenericResidualPolynomial_map_coefficients f c) r hr

/-- Literal generic-line point compatibility for every old root parameter.
In particular `r` may be a conjugate of the chosen root. -/
theorem kollarResidualLinePoint_map
    {k l : Type u} [Field k] [Field l] (f : k →+* l) (c : Cubic k 4)
    (r : AdjoinRoot (kollarGenericResidualPolynomial c)) :
    (fun i => kollarResidualRootBaseChange f c
      (((fun i => AdjoinRoot.of (kollarGenericResidualPolynomial c)
          (algebraMap k (FractionRing (MvPolynomial (Fin 3) k)) (kollarBasePoint k i))) +
        r • (fun i => AdjoinRoot.of (kollarGenericResidualPolynomial c)
          (kollarGenericProjectiveLineDirection k i))) i)) =
      (fun i => AdjoinRoot.of (kollarGenericResidualPolynomial (c.map f))
        (algebraMap l (FractionRing (MvPolynomial (Fin 3) l)) (kollarBasePoint l i))) +
        (kollarResidualRootBaseChange f c r) •
          (fun i => AdjoinRoot.of (kollarGenericResidualPolynomial (c.map f))
            (kollarGenericProjectiveLineDirection l i)) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  rw [kollarResidualRootBaseChange_of, kollarResidualRootBaseChange_of]
  rw [congrFun (kollarGenericBasePoint_map_coefficients f) i,
    congrFun (kollarGenericProjectiveLineDirection_map_coefficients f) i]

end AllCharacteristics
