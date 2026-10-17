import PfaffianDescent.QuadraticSecant
import PfaffianDescent.QuarticBinaryForms
import PfaffianDescent.ProjectiveClosedPointCoordinates
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.ProjectivePoints

/-! SOURCE ONLY / UNVERIFIED. Direct polynomial quadratic secant on the
actual cubic, without constructing a cubic tensor. The quadratic-generator
basis, binary restriction, residual factor and original section are derived.
-/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private def binaryLineRestriction
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (a b : Fin 4 → K) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval (fun i => C (a i) * X 0 + C (b i) * X 1) p

private theorem binaryLineRestriction_homogeneous
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (a b : Fin 4 → K) : (binaryLineRestriction p a b).IsHomogeneous 3 := by
  have h := hp.aeval (fun i => C (a i) * X (0 : Fin 2) + C (b i) * X (1 : Fin 2))
    (fun i => (isHomogeneous_C_mul_X (a i) (0 : Fin 2)).add
      (isHomogeneous_C_mul_X (b i) (1 : Fin 2)))
  simpa only [binaryLineRestriction, one_mul] using h

private theorem binaryLineRestriction_eval
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (a b : Fin 4 → K) (s t : L) :
    MvPolynomial.aeval ![s, t] (binaryLineRestriction p a b) =
      MvPolynomial.aeval (fun i => algebraMap K L (a i) * s + algebraMap K L (b i) * t) p := by
  have h : (MvPolynomial.aeval ![s, t]).comp
      (MvPolynomial.aeval (fun i => C (a i) * X 0 + C (b i) * X 1)) =
      MvPolynomial.aeval (fun i => algebraMap K L (a i) * s + algebraMap K L (b i) * t) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X, map_add, map_mul, aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact AlgHom.congr_fun h p

private theorem binaryCubic_quadraticGenerator_groundZero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (alpha : L)
    (hspan : ∀ z : L, ∃ a b : K, z = algebraMap K L a + algebraMap K L b * alpha)
    (hind : ∀ a b : K, algebraMap K L a + algebraMap K L b * alpha = 0 → a = 0 ∧ b = 0)
    (H : MvPolynomial (Fin 2) K) (hH : H.IsHomogeneous 3)
    (hroot : MvPolynomial.aeval ![1, alpha] H = 0) :
    ∃ z : Fin 2 → K, z ≠ 0 ∧ MvPolynomial.aeval z H = 0 := by
  classical
  let f := algebraMap K L
  obtain ⟨r, s, hrs⟩ := hspan (alpha ^ 2)
  obtain ⟨a, b, c, d, hExpansion⟩ := QuarticNet.binary_cubic_expansion H hH
  have hroot' : f a + alpha * f b + alpha ^ 2 * f c + alpha ^ 3 * f d = 0 := by
    rw [hExpansion] at hroot
    simpa only [map_add, map_mul, map_pow, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_pow,
      one_mul, mul_comm, mul_left_comm, mul_assoc] using hroot
  have he : f (a + r * c + r * s * d) +
      f (b + s * c + (r + s ^ 2) * d) * alpha = 0 := by
    simp only [map_add, map_mul, map_pow]
    linear_combination hroot' - (f c + (alpha + f s) * f d) * hrs
  obtain ⟨h0, h1⟩ := hind _ _ he
  have ha : a = -(r * c + r * s * d) := by linear_combination h0
  have hb : b = -(s * c + (r + s ^ 2) * d) := by linear_combination h1
  have hfactor : H = (X 1 ^ 2 - C s * X 0 * X 1 - C r * X 0 ^ 2) *
      (C d * X 1 + C (c + s * d) * X 0) := by
    rw [hExpansion, ha, hb]
    simp only [map_neg, map_add, map_mul, map_pow]
    ring
  by_cases hz : H = 0
  · refine ⟨![1, 0], ?_, by rw [hz]; exact map_zero _⟩
    intro heq
    have hzero : (1 : K) = 0 := by
      have h := congrFun heq (0 : Fin 2)
      simpa only [Matrix.cons_val_zero, Pi.zero_apply] using h
    exact (one_ne_zero : (1 : K) ≠ 0) hzero
  let z : Fin 2 → K := ![d, -(c + s * d)]
  have hzne : z ≠ 0 := by
    intro h
    have hd : d = 0 := by simpa only [z, Matrix.cons_val_zero, Pi.zero_apply] using congrFun h 0
    have hc : c = 0 := by
      have hh := congrFun h 1
      change -(c + s * d) = 0 at hh
      simpa only [hd, mul_zero, add_zero, neg_eq_zero] using hh
    apply hz
    rw [hfactor]
    simp only [hc, hd, mul_zero, add_zero, map_zero, zero_mul, mul_zero]
  have hlinear : MvPolynomial.aeval z (C d * X 1 + C (c + s * d) * X 0) = 0 := by
    simp only [z, map_add, map_mul, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring
  refine ⟨z, hzne, ?_⟩
  rw [hfactor, map_mul, hlinear, mul_zero]

private theorem ground_eval_of_mapped_coordinates
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (y : Fin 4 → K) (x : Fin 4 → L)
    (hcoord : (fun i => algebraMap K L (y i)) = x)
    (he : p.eval₂ (algebraMap K L) x = 0) : p.eval₂ (RingHom.id K) y = 0 := by
  apply (algebraMap K L).injective
  rw [map_zero, hom_eval₂, RingHom.comp_id, hcoord]
  exact he

private theorem normalized_quadratic_coordinates_polynomial_secant
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hdim : finrank K L ≤ 2) (x : Fin 4 → L) (j : Fin 4) (hxj : x j = 1)
    (he : p.eval₂ (algebraMap K L) x = 0) :
    ∃ y : Fin 4 → K, y ≠ 0 ∧ p.eval₂ (RingHom.id K) y = 0 := by
  classical
  have hpos : 0 < finrank K L := Module.finrank_pos
  have hcases : finrank K L = 1 ∨ finrank K L = 2 := by omega
  rcases hcases with hdimOne | hdimTwo
  · have hsurj := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdimOne).2
    choose y hy using fun i => hsurj (x i)
    have hcoord : (fun i => algebraMap K L (y i)) = x := funext hy
    refine ⟨y, ?_, ground_eval_of_mapped_coordinates p y x hcoord he⟩
    intro hyzero
    have hzero : (1 : L) = 0 := by
      rw [← hxj, ← hy j, hyzero]
      exact map_zero _
    exact (one_ne_zero : (1 : L) ≠ 0) hzero
  obtain ⟨alpha, hspan, hind⟩ := quadratic_generator hdimTwo
  choose a b hab using fun i => hspan (x i)
  have hnorm : algebraMap K L (a j - 1) + algebraMap K L (b j) * alpha = 0 := by
    rw [map_sub, map_one]
    have h := hab j
    rw [hxj] at h
    linear_combination -h
  obtain ⟨haj, hbj⟩ := hind _ _ hnorm
  have hajOne : a j = 1 := sub_eq_zero.mp haj
  by_cases hbzero : b = 0
  · have hcoord : (fun i => algebraMap K L (a i)) = x := by
      funext i
      simpa only [hbzero, Pi.zero_apply, map_zero, zero_mul, add_zero] using (hab i).symm
    refine ⟨a, ?_, ground_eval_of_mapped_coordinates p a x hcoord he⟩
    intro hazero
    have hzero : (1 : K) = 0 := hajOne.symm.trans (congrFun hazero j)
    exact (one_ne_zero : (1 : K) ≠ 0) hzero
  let H := binaryLineRestriction p a b
  have hH : H.IsHomogeneous 3 := binaryLineRestriction_homogeneous p hp a b
  have hparam : (fun i => algebraMap K L (a i) * (1 : L) + algebraMap K L (b i) * alpha) = x := by
    funext i
    simpa only [mul_one] using (hab i).symm
  have hroot : MvPolynomial.aeval ![1, alpha] H = 0 := by
    change MvPolynomial.aeval ![1, alpha] (binaryLineRestriction p a b) = 0
    rw [binaryLineRestriction_eval, hparam, MvPolynomial.aeval_def]
    exact he
  obtain ⟨z, hzne, hzvalue⟩ := binaryCubic_quadraticGenerator_groundZero alpha hspan hind H hH hroot
  let y : Fin 4 → K := fun i => a i * z 0 + b i * z 1
  have hyne : y ≠ 0 := by
    intro hyzero
    have hz0 : z 0 = 0 := by
      have h := congrFun hyzero j
      simpa only [y, hajOne, hbj, one_mul, zero_mul, add_zero, Pi.zero_apply] using h
    have hz1 : z 1 = 0 := by
      obtain ⟨i, hbi⟩ : ∃ i, b i ≠ 0 := by
        by_contra h
        push Not at h
        exact hbzero (funext h)
      have h := congrFun hyzero i
      have hprod : b i * z 1 = 0 := by
        simpa only [y, hz0, mul_zero, zero_add, Pi.zero_apply] using h
      exact (mul_eq_zero.mp hprod).resolve_left hbi
    apply hzne
    funext i
    fin_cases i
    · exact hz0
    · exact hz1
  have hid : (fun i => algebraMap K K (a i) * z 0 + algebraMap K K (b i) * z 1) = y := by
    funext i
    change algebraMap K K (a i) * z 0 + algebraMap K K (b i) * z 1 =
      a i * z 0 + b i * z 1
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hzvec : ![z 0, z 1] = z := by funext i; fin_cases i <;> rfl
  have hyvalue : MvPolynomial.aeval y p = 0 := by
    have h := binaryLineRestriction_eval p a b (z 0) (z 1)
    rw [hzvec, hid] at h
    exact h.symm.trans hzvalue
  refine ⟨y, hyne, ?_⟩
  simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self] using hyvalue

/-- Actual closed points of degree<=2 give a rational section of the SAME
original cubic by a direct polynomial quadratic secant. No cubic tensor,
Euler conversion, degree-five/Pfaffian descent or geometric certificate. -/
theorem originalCubic_closedPoint_degree_le_two_polynomialSecant_has_section
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 ≤ 2) :
    ∃ s : Spec (.of K) ⟶ hypersurface p hp, s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  classical
  let S := hypersurface p hp
  let I := equationIdeal p hp
  let L := S.residueField P.1
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  letI : Module.Finite K L := closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  letI hclosed : IsClosedImmersion (S.fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  have hdim : finrank K L ≤ 2 :=
    (closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) P).trans_le hP
  obtain ⟨j, x, hxj, _hgen, he⟩ := @closed_projective_point_generating_coordinates
    K L (inferInstance : Field K) (inferInstance : Field L)
    (pointAlgebra (hypersurfaceToBase p hp) P.1) (Fin 4)
    I (S.fromSpecResidueField P.1) hclosed
    (pointAlgebra_spec (hypersurfaceToBase p hp) P.1).symm
  have hpx : p.eval₂ (algebraMap K L) x = 0 := he p (Ideal.subset_span (Set.mem_singleton p))
  obtain ⟨y, hy, hpy⟩ := normalized_quadratic_coordinates_polynomial_secant p hp hdim x j hxj hpx
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id K) p hp y hy hpy
  exact ⟨s, by simpa using hs⟩

end PfaffianDescent.Coray
