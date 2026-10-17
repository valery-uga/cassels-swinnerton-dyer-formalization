import PfaffianDescent.HomogeneousIdealPieces
import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.VoisinGenericQuadraticEvaluation
import PfaffianDescent.VoisinVeryAmpleQuadraticSections
import PfaffianDescent.HomogeneousIdealPieceCoefficientBaseChange
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Quadratic sections containing Voisin's fixed curve

The fixed divisor extracted from a failed degree-eight quadratic system is
represented by a homogeneous ideal `C`.  This file packages the degree-two
part of `C` as the polynomial moving system used in the disjoint branch of
Voisin's fixed-component argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Homogeneous quadrics whose projective zero scheme contains the fixed
curve represented by `C`. -/
noncomputable def fixedCurveQuadraticPolynomialSystem
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  (homogeneousIdealPiece C 2).map
    (homogeneousSubmodule (Fin 4) K 2).subtype

/-- Passing from the intrinsic degree-two ideal piece to its polynomial
image does not change its dimension. -/
theorem finrank_fixedCurveQuadraticPolynomialSystem
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    finrank K (fixedCurveQuadraticPolynomialSystem C) =
      finrank K (homogeneousIdealPiece C 2) := by
  exact Submodule.finrank_map_subtype_eq
    (homogeneousSubmodule (Fin 4) K 2) (homogeneousIdealPiece C 2)

theorem mem_fixedCurveQuadraticPolynomialSystem_iff
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (q : MvPolynomial (Fin 4) K) :
    q ∈ fixedCurveQuadraticPolynomialSystem C ↔
      q.IsHomogeneous 2 ∧ q ∈ C.toIdeal := by
  constructor
  · rintro ⟨q', hq', rfl⟩
    exact ⟨q'.property, hq'⟩
  · rintro ⟨hq, hqC⟩
    let q' : homogeneousSubmodule (Fin 4) K 2 := ⟨q, hq⟩
    have hq' : q' ∈ homogeneousIdealPiece C 2 := by
      exact (mem_homogeneousIdealPiece_iff C 2 q').mpr hqC
    exact ⟨q', hq', rfl⟩

theorem fixedCurveQuadraticPolynomialSystem_isHomogeneous
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    ∀ q ∈ fixedCurveQuadraticPolynomialSystem C, q.IsHomogeneous 2 := by
  intro q hq
  exact (mem_fixedCurveQuadraticPolynomialSystem_iff C q).mp hq |>.1

/-- The quadratic system containing a fixed curve is finite-dimensional,
because every member lies in the ten-dimensional homogeneous quadratic
space. -/
noncomputable instance fixedCurveQuadraticPolynomialSystem_finiteDimensional
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    FiniteDimensional K (fixedCurveQuadraticPolynomialSystem C) := by
  let W := fixedCurveQuadraticPolynomialSystem C
  let H := homogeneousSubmodule (Fin 4) K 2
  let lift : W →ₗ[K] H :=
    { toFun := fun q =>
        ⟨q.1, fixedCurveQuadraticPolynomialSystem_isHomogeneous C q.1 q.2⟩
      map_add' := by intro q r; ext <;> rfl
      map_smul' := by intro a q; ext <;> rfl }
  have hlift : Function.Injective lift := by
    intro q r hqr
    apply Subtype.ext
    exact congrArg (fun z : H => z.1) hqr
  letI : FiniteDimensional K H :=
    (Submodule.fg_iff_finiteDimensional H).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) K 2)
  exact Module.Finite.of_injective lift hlift

/-- A fixed-curve quadric cannot be a nonzero multiple of the cubic
equation; this is the separation hypothesis required by the generic
incidence theorem. -/
theorem fixedCurveQuadraticPolynomialSystem_separates_cubic
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    ∀ q ∈ fixedCurveQuadraticPolynomialSystem C,
      q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → q = 0 := by
  intro q hq hqp
  exact homogeneousQuadratic_separate_cubic_equation p q hp
    ((mem_fixedCurveQuadraticPolynomialSystem_iff C q).mp hq).1 hqp

/-- Every member of the fixed-curve quadratic system vanishes at an affine
cone point of the fixed curve. -/
theorem fixedCurveQuadraticPolynomialSystem_aeval_eq_zero
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : Fin 4 → K)
    (hx : ∀ f ∈ C.toIdeal, MvPolynomial.aeval x f = 0)
    (q : fixedCurveQuadraticPolynomialSystem C) :
    MvPolynomial.aeval x q.1 = 0 := by
  apply hx q.1
  exact (mem_fixedCurveQuadraticPolynomialSystem_iff C q.1).mp q.2 |>.2

/-- Two distinct projective points on the fixed curve bound its quadratic
ideal piece by eight dimensions. -/
theorem fixedCurveQuadraticPolynomialSystem_finrank_le_eight
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x y : cubicSurfaceAffinePoints p)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (hx : ∀ f ∈ C.toIdeal, MvPolynomial.aeval x.1 f = 0)
    (hy : ∀ f ∈ C.toIdeal, MvPolynomial.aeval y.1 f = 0) :
    finrank K (fixedCurveQuadraticPolynomialSystem C) ≤ 8 := by
  apply homogeneousQuadraticPolynomialSubmodule_finrank_le_eight_of_pointwise_vanishing
    p x y hdir (fixedCurveQuadraticPolynomialSystem C)
    (fixedCurveQuadraticPolynomialSystem_isHomogeneous C)
  intro q
  exact ⟨fixedCurveQuadraticPolynomialSystem_aeval_eq_zero C x.1 hx q,
    fixedCurveQuadraticPolynomialSystem_aeval_eq_zero C y.1 hy q⟩

/-- The quadratic ideal of a relevant height-two prime curve has dimension at
most eight.  The two projectively distinct points required by quadratic
separation are now produced internally from the curve ideal. -/
theorem fixedCurveQuadraticPolynomialSystem_finrank_le_eight_of_prime_height_two
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hheight : C.toIdeal.height = 2) :
    finrank K (fixedCurveQuadraticPolynomialSystem C) ≤ 8 := by
  obtain ⟨j, x, k, y, hxj, hxC, hyk, hyC, hdir⟩ :=
    homogeneousPrime_exists_two_distinct_normalized_coordinates
      C hprime hrelevant hheight
  have hx0 : x ≠ 0 := by
    intro h
    have := congrFun h j
    simp [hxj] at this
  have hy0 : y ≠ 0 := by
    intro h
    have := congrFun h k
    simp [hyk] at this
  let xp : cubicSurfaceAffinePoints p := ⟨x, by
    constructor
    · simpa [MvPolynomial.aeval_def] using hxC p hCp
    · exact hx0⟩
  let yp : cubicSurfaceAffinePoints p := ⟨y, by
    constructor
    · simpa [MvPolynomial.aeval_def] using hyC p hCp
    · exact hy0⟩
  apply fixedCurveQuadraticPolynomialSystem_finrank_le_eight p C xp yp hdir
  · intro f hf
    simpa [MvPolynomial.aeval_def] using hxC f hf
  · intro f hf
    simpa [MvPolynomial.aeval_def] using hyC f hf

/-- A height-two homogeneous prime acquires a relevant homogeneous prime
above it after extension to the algebraic closure, without changing its
height.  Faithful flatness gives a prime lying over the original ideal;
integrality makes that prime minimal over the extended ideal, and the
going-down height formula has zero-dimensional fibre. -/
theorem exists_algebraicClosure_homogeneousPrime_over_height_two
    {k : Type u} [Field k]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hprime : C.toIdeal.IsPrime) (hheight : C.toIdeal.height = 2) :
    let J : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) :=
      HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom
          (algebraMap k (AlgebraicClosure k))) C
    ∃ P : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)),
      P.toIdeal.IsPrime ∧
      (¬ HomogeneousIdeal.irrelevant
        (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) ≤ P) ∧
      P.toIdeal.height = 2 ∧ J ≤ P := by
  dsimp only
  let R := MvPolynomial (Fin 4) k
  let S := MvPolynomial (Fin 4) (AlgebraicClosure k)
  letI : Module.FaithfullyFlat R S :=
    mvPolynomial_coefficientExtension_faithfullyFlat
  obtain ⟨P₀, hP₀prime, hP₀over⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) C.toIdeal
  letI : P₀.IsPrime := hP₀prime
  letI : P₀.LiesOver C.toIdeal := hP₀over
  have hP₀min : P₀ ∈
      (C.toIdeal.map (algebraMap R S)).minimalPrimes := by
    rw [Ideal.LiesOver.over (p := C.toIdeal) (P := P₀)]
    exact Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) P₀
  let q := Ideal.Quotient.mk (C.toIdeal.map (algebraMap R S))
  have hfibmin : P₀.map q ∈
      minimalPrimes (S ⧸ C.toIdeal.map (algebraMap R S)) := by
    have hsets := Ideal.minimalPrimes_map_of_surjective
      (f := q) Ideal.Quotient.mk_surjective
      (C.toIdeal.map (algebraMap R S))
    rw [Ideal.map_quotient_self] at hsets
    change P₀.map q ∈
      (⊥ : Ideal (S ⧸ C.toIdeal.map (algebraMap R S))).minimalPrimes
    rw [hsets]
    refine ⟨P₀, ?_, rfl⟩
    simpa only [q, Ideal.mk_ker, sup_idem] using hP₀min
  have hfibheight : (P₀.map q).height = 0 := by
    letI : (P₀.map q).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        simpa only [q, Ideal.mk_ker] using hP₀min.le)
    exact Ideal.height_eq_zero_iff.mpr hfibmin
  have hP₀height : P₀.height = 2 := by
    have h :=
      Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown C.toIdeal P₀
    rw [hheight,
      show Ideal.Quotient.mk (C.toIdeal.map (algebraMap R S)) = q from rfl,
      hfibheight, add_zero] at h
    exact h
  let P := P₀.homogeneousCore
    (homogeneousSubmodule (Fin 4) (AlgebraicClosure k))
  let J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom
        (algebraMap k (AlgebraicClosure k))) C
  have hJP₀ : J.toIdeal ≤ P₀ := by
    change C.toIdeal.map (algebraMap R S) ≤ P₀
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def,
      ← Ideal.LiesOver.over (p := C.toIdeal) (P := P₀)]
  have hJP : J ≤ P :=
    (Ideal.homogeneousCore.gc _ J P₀).mp hJP₀
  have hPcore : P.toIdeal = P₀ := by
    apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    exact hP₀min.2 ⟨hP₀prime.homogeneousCore,
      show J.toIdeal ≤ P.toIdeal from hJP⟩
      (Ideal.toIdeal_homogeneousCore_le _ _)
  have hPprime : P.toIdeal.IsPrime := hP₀prime.homogeneousCore
  have hPh : P.toIdeal.height = 2 := by rw [hPcore, hP₀height]
  exact ⟨P, hPprime,
    homogeneousIdeal_relevant_of_height_le_two P hPh.le, hPh, hJP⟩

/-- The dimension-eight bound for the quadratic ideal of a height-two prime
curve holds over an arbitrary field.  Extend to the algebraic closure, use a
height-two geometric prime component and two geometric points there, then
descend the dimension inequality through injective coefficient extension. -/
theorem fixedCurveQuadraticPolynomialSystem_finrank_le_eight_of_prime_height_two_arbitrary_field
    {k : Type u} [Field k]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hprime : C.toIdeal.IsPrime) (hheight : C.toIdeal.height = 2) :
    finrank k (fixedCurveQuadraticPolynomialSystem C) ≤ 8 := by
  let J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom
        (algebraMap k (AlgebraicClosure k))) C
  obtain ⟨P, hPprime, hPrelevant, hPheight, hJP⟩ :=
    exists_algebraicClosure_homogeneousPrime_over_height_two C hprime hheight
  have hJ : C.toIdeal.map
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) = J.toIdeal := by
    change C.toIdeal.map
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) =
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom
          (algebraMap k (AlgebraicClosure k))) C).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  have hpiece : homogeneousIdealPiece J 2 ≤ homogeneousIdealPiece P 2 := by
    intro q hq
    apply (mem_homogeneousIdealPiece_iff P 2 q).mpr
    exact hJP ((mem_homogeneousIdealPiece_iff J 2 q).mp hq)
  rw [finrank_fixedCurveQuadraticPolynomialSystem C]
  calc
    finrank k (homogeneousIdealPiece C 2) ≤
        finrank (AlgebraicClosure k) (homogeneousIdealPiece J 2) :=
      homogeneousIdealPiece_finrank_le_coefficientExtension C J hJ 2
    _ ≤ finrank (AlgebraicClosure k) (homogeneousIdealPiece P 2) :=
      Submodule.finrank_mono hpiece
    _ = finrank (AlgebraicClosure k)
        (fixedCurveQuadraticPolynomialSystem P) :=
      (finrank_fixedCurveQuadraticPolynomialSystem P).symm
    _ ≤ 8 :=
      fixedCurveQuadraticPolynomialSystem_finrank_le_eight_of_prime_height_two
        (0 : MvPolynomial (Fin 4) (AlgebraicClosure k)) P (by simp)
          hPprime hPrelevant hPheight

/-- Numerical close of the disjoint branch once generic incidence has forced
nine fixed-curve quadrics: two distinct points on the curve give the
contradictory upper bound eight. -/
theorem fixedCurveQuadraticPolynomialSystem_disjoint_contradiction
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x y : cubicSurfaceAffinePoints p)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (hx : ∀ f ∈ C.toIdeal, MvPolynomial.aeval x.1 f = 0)
    (hy : ∀ f ∈ C.toIdeal, MvPolynomial.aeval y.1 f = 0)
    (hnine : 9 ≤ finrank K (fixedCurveQuadraticPolynomialSystem C)) : False := by
  have height := fixedCurveQuadraticPolynomialSystem_finrank_le_eight
    p C x y hdir hx hy
  omega

/-- The distinguished quadric in fixed-divisor data belongs to the
quadratic system containing the fixed curve. -/
theorem DegreeEightDivisorFixedSubschemeData.q_mem_fixedCurveQuadraticPolynomialSystem
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (h : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp) :
    q ∈ fixedCurveQuadraticPolynomialSystem C := by
  rcases h with ⟨hq, _, _, _, _, _, _, _, _, hspan, _, _, _⟩
  apply (mem_fixedCurveQuadraticPolynomialSystem_iff C q).mpr
  exact ⟨hq, hspan (Ideal.subset_span (by simp))⟩

/-- In fact every quadric vanishing on the chosen degree-eight presentation
belongs to the quadratic system containing the fixed curve. -/
theorem DegreeEightDivisorFixedSubschemeData.vanishing_le_fixedCurveQuadraticPolynomialSystem
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (h : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp) :
    homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2 ≤
      fixedCurveQuadraticPolynomialSystem C := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hall⟩
  intro r hr
  obtain ⟨hrhom, hrC, -⟩ := hall r hr
  exact (mem_fixedCurveQuadraticPolynomialSystem_iff C r).mpr ⟨hrhom, hrC⟩

/-- The fixed curve extracted from failed degree-eight proper intersection
has at most eight independent quadratic equations, over the original
coefficient field. -/
theorem DegreeEightDivisorFixedSubschemeData.finrank_fixedCurveQuadraticPolynomialSystem_le_eight
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (h : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp) :
    finrank K (fixedCurveQuadraticPolynomialSystem C) ≤ 8 := by
  rcases h with ⟨_, _, _, _, hprime, _, hheight, _, _, _, _, _, _⟩
  exact
    fixedCurveQuadraticPolynomialSystem_finrank_le_eight_of_prime_height_two_arbitrary_field
      C hprime hheight

/-- Nine fixed-curve quadrics are impossible for the divisor extracted from
the failed degree-eight proper-intersection condition. -/
theorem DegreeEightDivisorFixedSubschemeData.not_nine_le_finrank_fixedCurveQuadraticPolynomialSystem
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (h : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp) :
    ¬ 9 ≤ finrank K (fixedCurveQuadraticPolynomialSystem C) := by
  intro hnine
  have height :=
    h.finrank_fixedCurveQuadraticPolynomialSystem_le_eight
      p hp D₈ x q C hCp
  omega

/-- The fixed-curve quadratic system contains the whole pencil through the
length-eight datum, and therefore has dimension at least two. -/
theorem DegreeEightDivisorFixedSubschemeData.two_le_finrank_fixedCurveQuadraticPolynomialSystem
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    [FiniteDimensional K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hA : finrank K Γ(D₈.val.subscheme, ⊤) = 8)
    (h : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp) :
    2 ≤ finrank K (fixedCurveQuadraticPolynomialSystem C) := by
  calc
    2 ≤ finrank K (LinearMap.ker
        (homogeneousSectionRestriction (K := K) x 2)) :=
      quadric_degree_eight_vanishing_sections_finrank x hA
    _ = finrank K (homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(D₈.val.subscheme, ⊤)) (sigma := Fin 4) x 2) := by
      rw [homogeneousVanishingPolynomialSubmodule_finrank]
    _ ≤ finrank K (fixedCurveQuadraticPolynomialSystem C) :=
      Submodule.finrank_mono
        (h.vanishing_le_fixedCurveQuadraticPolynomialSystem p hp D₈ x q C hCp)

/-- Intrinsic form of the preceding lower bound, matching the subspace used
by the Grassmannian spreading construction. -/
theorem DegreeEightDivisorFixedSubschemeData.two_le_finrank_homogeneousIdealPiece
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    [FiniteDimensional K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hA : finrank K Γ(D₈.val.subscheme, ⊤) = 8)
    (h : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp) :
    2 ≤ finrank K (homogeneousIdealPiece C 2) := by
  rw [← finrank_fixedCurveQuadraticPolynomialSystem C]
  exact h.two_le_finrank_fixedCurveQuadraticPolynomialSystem
    p hp D₈ x q C hCp hA

/-- A relevant height-two fixed curve has a good eight-point configuration
for its quadratic section system: evaluation on those points is injective.
This is the ground-field witness needed by the proper-incidence argument for
each fixed divisor class. -/
theorem exists_eight_fixedCurveQuadraticPolynomialSystem_evaluation_injective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal) (hCprime : C.toIdeal.IsPrime)
    (hCrelevant : ¬ HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hCheight : C.toIdeal.height = 2) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), u.card = 8 ∧
      Function.Injective ((finsetEvaluation u).comp
        (cubicSurfacePointEvaluation p (fixedCurveQuadraticPolynomialSystem C))) ∧
      ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : K, y.1 ≠ a • x.1 := by
  apply exists_eight_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions
    p hp hne hprime (by decide)
    (fixedCurveQuadraticPolynomialSystem C)
    (fixedCurveQuadraticPolynomialSystem_isHomogeneous C)
    (fixedCurveQuadraticPolynomialSystem_separates_cubic p hp C)
  exact fixedCurveQuadraticPolynomialSystem_finrank_le_eight_of_prime_height_two
    p C hCp hCprime hCrelevant hCheight

/-- The fixed-component output used in the degree-eight argument carries its
own prime height-two curve certificate, so the good eight-point evaluation
configuration applies directly to that output. -/
theorem DegreeEightDivisorFixedSubschemeData.exists_eight_fixedCurveQuadraticPolynomialSystem_evaluation_injective
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra K Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) K)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (h : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp) :
    ∃ u : Finset (cubicSurfaceAffinePoints p), u.card = 8 ∧
      Function.Injective ((finsetEvaluation u).comp
        (cubicSurfacePointEvaluation p (fixedCurveQuadraticPolynomialSystem C))) ∧
      ∀ a ∈ u, ∀ b ∈ u, a ≠ b → ∀ c : K, b.1 ≠ c • a.1 := by
  rcases h with ⟨_, _, _, _, hCprime, hCrelevant, hCheight, _, _, _, _, _, _⟩
  exact _root_.PfaffianDescent.exists_eight_fixedCurveQuadraticPolynomialSystem_evaluation_injective
    p hp hne hprime C hCp hCprime hCrelevant hCheight

/-- Even when the prime curve splits after extending the coefficient field,
one geometric prime component above it still supplies a quadratic system of
dimension at most eight, and hence an eight-point injective evaluation
configuration over the algebraic closure. -/
theorem exists_eight_algebraicClosure_fixedCurveQuadraticPolynomialSystem_evaluation_injective
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hCp : p ∈ C.toIdeal) (hCprime : C.toIdeal.IsPrime)
    (hCheight : C.toIdeal.height = 2)
    (pbarPrime : (Ideal.span
      ({p.map (algebraMap k (AlgebraicClosure k))} :
        Set (MvPolynomial (Fin 4) (AlgebraicClosure k)))).IsPrime) :
    let Cbar : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) :=
      HomogeneousIdeal.map (ambientCoefficientGradedRingHom
        (algebraMap k (AlgebraicClosure k))) C
    ∃ P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)),
      P.toIdeal.IsPrime ∧
      (¬ HomogeneousIdeal.irrelevant
        (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) ≤ P) ∧
      P.toIdeal.height = 2 ∧
      Cbar ≤ P ∧
      ∃ u : Finset (cubicSurfaceAffinePoints
          (p.map (algebraMap k (AlgebraicClosure k)))),
        u.card = 8 ∧
        Function.Injective ((finsetEvaluation u).comp
          (cubicSurfacePointEvaluation
            (p.map (algebraMap k (AlgebraicClosure k)))
            (fixedCurveQuadraticPolynomialSystem Cbar))) ∧
        ∀ x ∈ u, ∀ y ∈ u, x ≠ y → ∀ a : AlgebraicClosure k,
          y.1 ≠ a • x.1 := by
  dsimp only
  let φ : k →+* AlgebraicClosure k := algebraMap k (AlgebraicClosure k)
  let p' := p.map φ
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) :=
    HomogeneousIdeal.map (ambientCoefficientGradedRingHom φ) C
  obtain ⟨P, hPprime, hPrelevant, hPheight, hJP⟩ :=
    exists_algebraicClosure_homogeneousPrime_over_height_two C hCprime hCheight
  have hJ : C.toIdeal.map (MvPolynomial.map φ) = J.toIdeal := by
    change C.toIdeal.map (MvPolynomial.map φ) =
      (HomogeneousIdeal.map (ambientCoefficientGradedRingHom φ) C).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  have hpiece : homogeneousIdealPiece J 2 ≤ homogeneousIdealPiece P 2 := by
    intro q hq
    apply (mem_homogeneousIdealPiece_iff P 2 q).mpr
    exact hJP ((mem_homogeneousIdealPiece_iff J 2 q).mp hq)
  have hpJ : p' ∈ J.toIdeal := by
    rw [← hJ]
    exact Ideal.mem_map_of_mem (MvPolynomial.map φ) hCp
  have hpP : p' ∈ P.toIdeal := hJP hpJ
  have hdim : finrank (AlgebraicClosure k)
      (fixedCurveQuadraticPolynomialSystem J) ≤ 8 := by
    rw [finrank_fixedCurveQuadraticPolynomialSystem]
    calc
      finrank (AlgebraicClosure k) (homogeneousIdealPiece J 2) ≤
          finrank (AlgebraicClosure k) (homogeneousIdealPiece P 2) :=
        Submodule.finrank_mono hpiece
      _ = finrank (AlgebraicClosure k)
          (fixedCurveQuadraticPolynomialSystem P) :=
        (finrank_fixedCurveQuadraticPolynomialSystem P).symm
      _ ≤ 8 := fixedCurveQuadraticPolynomialSystem_finrank_le_eight_of_prime_height_two
        p' P hpP hPprime hPrelevant hPheight
  have hne' : p' ≠ 0 := by
    intro hzero
    apply hne
    apply MvPolynomial.map_injective φ φ.injective
    simpa [p'] using hzero
  have hhom' : p'.IsHomogeneous 3 := hp.map φ
  have hsel := exists_eight_cubicSurfaceAffinePoints_homogeneousSystem_evaluation_injective_independent_directions
    p' hhom' hne' pbarPrime (by decide)
    (fixedCurveQuadraticPolynomialSystem J)
    (fixedCurveQuadraticPolynomialSystem_isHomogeneous J)
    (fixedCurveQuadraticPolynomialSystem_separates_cubic p' hhom' J) hdim
  refine ⟨P, hPprime, hPrelevant, hPheight, hJP, hsel⟩

/-- For the actual fixed-component output on a smooth cubic, geometric
integrality of the cubic supplies the prime-surface hypothesis after
extension to the algebraic closure, so the geometric eight-point witness
needs no separate prime certificate for the extended cubic. -/
theorem DegreeEightDivisorFixedSubschemeData.exists_eight_algebraicClosure_fixedCurveQuadraticPolynomialSystem_evaluation_injective_of_smooth
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    [Algebra k Γ(D₈.val.subscheme, ⊤)]
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (q : MvPolynomial (Fin 4) k)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hCp : p ∈ C.toIdeal)
    (h : DegreeEightDivisorFixedSubschemeData p hp D₈ x q C hCp) :
    let Cbar : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) :=
      HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom
          (algebraMap k (AlgebraicClosure k))) C
    ∃ P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)),
      P.toIdeal.IsPrime ∧
      (¬ HomogeneousIdeal.irrelevant
        (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) ≤ P) ∧
      P.toIdeal.height = 2 ∧
      Cbar ≤ P ∧
      ∃ u : Finset (cubicSurfaceAffinePoints
          (p.map (algebraMap k (AlgebraicClosure k)))),
        u.card = 8 ∧
        Function.Injective ((finsetEvaluation u).comp
          (cubicSurfacePointEvaluation
            (p.map (algebraMap k (AlgebraicClosure k)))
            (fixedCurveQuadraticPolynomialSystem Cbar))) ∧
        ∀ a ∈ u, ∀ b ∈ u, a ≠ b → ∀ c : AlgebraicClosure k,
          b.1 ≠ c • a.1 := by
  rcases h with ⟨_, _, _, _, hCprime, _, hCheight, _, _, _, _, _, _⟩
  exact exists_eight_algebraicClosure_fixedCurveQuadraticPolynomialSystem_evaluation_injective
    p hp hne C hCp hCprime hCheight
    (principalIdeal_map_prime_of_smooth_homogeneous_cubic
      (algebraMap k (AlgebraicClosure k)) p hp hne)

end PfaffianDescent
