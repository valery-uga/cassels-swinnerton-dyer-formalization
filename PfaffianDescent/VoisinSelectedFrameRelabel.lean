import PfaffianDescent.VoisinQuadraticKernelSpecialization
import PfaffianDescent.VoisinQuadraticKernelBasisIdeal
import PfaffianDescent.VoisinIntrinsicQuadraticKernelIdeal

/-! Pointwise permutation invariance of the actual selected quadratic frame. -/

namespace PfaffianDescent

open MvPolynomial AllCharacteristics.UniversalHomogeneous
  AllCharacteristics.HomogeneousProjective

universe u v

/-- On any full-rank selected minor chart, its explicit two-equation frame
generates the intrinsic cubic-plus-quadratic intersection ideal. -/
theorem intrinsicEightPointTripleIdeal_eq_minorFrame
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m y).det)
    (p : MvPolynomial (Fin 4) R) :
    intrinsicEightPointTripleIdeal p y =
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients
        (eightPointQuadraticEvaluationKernelBasis m y hm i).1))) :=
  intrinsicEightPointTripleIdeal_eq_basis p y
    (eightPointQuadraticEvaluationKernelBasis m y hm)

/-- The actual selected determinant-open cubic--quadric--quadric family is
the intrinsic projective intersection attached to its eight coordinate
sections. This identifies the existing family without choosing its frame. -/
theorem selectedRelativeTripleIntersection_eq_intrinsic
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R)
    (p : MvPolynomial (Fin 4) (Localization.Away (quadraticMinorDet m y)))
    (hp : p.IsHomogeneous 3) :
    let S := Localization.Away (quadraticMinorDet m y)
    let yS : Fin 8 → Fin 4 → S :=
      fun k j => algebraMap R S (y k j)
    scheme (intrinsicEightPointTripleHomogeneousIdeal p hp yS) =
    relativeTripleIntersectionFamily p
      (quadraticSelectedOpenPolynomial m y 0)
      (quadraticSelectedOpenPolynomial m y 1) hp
      (quadraticSelectedOpenPolynomial_isHomogeneous m y 0)
      (quadraticSelectedOpenPolynomial_isHomogeneous m y 1) := by
  dsimp only
  simpa only [quadraticSelectedOpenPolynomial] using
    (intrinsicEightPointTripleScheme_eq_relative_of_basis p hp
      (fun k j => algebraMap R
        (Localization.Away (quadraticMinorDet m y)) (y k j))
      (quadraticSelectedOpenFullKernelBasis m y))

/-- At every field-valued point of the determinant open, the specialized
selected equations generate the intrinsic cubic-plus-kernel ideal of the
specialized eight-point configuration. -/
theorem intrinsicEightPointTripleIdeal_eq_specializedSelectedFrame
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (p : MvPolynomial (Fin 4) F) :
    intrinsicEightPointTripleIdeal p (fun k j => f (y k j)) =
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      (quadraticSelectedOpenPolynomial m y i).map
        (quadraticMinorSelectedPointLift m y f hm)))) := by
  let b := quadraticSelectedOpenBasisSpecializedBasis m y f hm
  have h := intrinsicEightPointTripleIdeal_eq_basis p
    (fun k j => f (y k j)) b
  have hframe :
      (fun i : Fin 2 =>
        (quadraticSelectedOpenPolynomial m y i).map
          (quadraticMinorSelectedPointLift m y f hm)) =
      (fun i => quadraticPolynomialOfCoefficients (b i).1) := by
    funext i
    rw [quadraticSelectedOpenPolynomial_map_selectedPoint]
    simp only [b, quadraticSelectedOpenBasisSpecializedBasis_apply]
  rw [hframe]
  exact h

/-- On a selected full-rank minor chart, the intrinsic intersection ideal
commutes with specialization to a field-valued point of that chart. -/
theorem intrinsicEightPointTripleIdeal_map_selectedPoint
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (p : MvPolynomial (Fin 4)
      (Localization.Away (quadraticMinorDet m y))) :
    let S := Localization.Away (quadraticMinorDet m y)
    let yS : Fin 8 → Fin 4 → S :=
      fun k j => algebraMap R S (y k j)
    let g := quadraticMinorSelectedPointLift m y f hm
    (intrinsicEightPointTripleIdeal p yS).map (MvPolynomial.map g) =
      intrinsicEightPointTripleIdeal (p.map g)
        (fun k j => f (y k j)) := by
  dsimp only
  let S := Localization.Away (quadraticMinorDet m y)
  let yS : Fin 8 → Fin 4 → S :=
    fun k j => algebraMap R S (y k j)
  let g := quadraticMinorSelectedPointLift m y f hm
  have hlocal : intrinsicEightPointTripleIdeal p yS =
      Ideal.span (insert p (Set.range (fun i : Fin 2 =>
        quadraticSelectedOpenPolynomial m y i))) := by
    simpa only [yS, quadraticSelectedOpenPolynomial] using
      (intrinsicEightPointTripleIdeal_eq_basis p yS
        (quadraticSelectedOpenFullKernelBasis m y))
  rw [hlocal, Ideal.map_span]
  have himage :
      (MvPolynomial.map g) ''
          (insert p (Set.range (fun i : Fin 2 =>
            quadraticSelectedOpenPolynomial m y i))) =
        insert (p.map g) (Set.range (fun i : Fin 2 =>
          (quadraticSelectedOpenPolynomial m y i).map g)) := by
    ext t
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_range]
    aesop
  rw [himage]
  exact (intrinsicEightPointTripleIdeal_eq_specializedSelectedFrame
    m y f hm (p.map g)).symm

/-- Over any commutative chart ring, if both chosen minors are units, the
quadratic pencil ideal is independent of the ordering and of the minor. -/
theorem quadraticKernelMinorIdeal_relabel
    {R : Type u} [CommRing R]
    (m n : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (σ : Equiv.Perm (Fin 8))
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m y).det)
    (hn : IsUnit (eightPointQuadraticEvaluationMinor n
      (fun k => y (σ k))).det)
    (p : MvPolynomial (Fin 4) R) :
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients
        (eightPointQuadraticEvaluationKernelBasis n
          (fun k => y (σ k)) hn i).1))) =
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients
        (eightPointQuadraticEvaluationKernelBasis m y hm i).1))) :=
  ideal_span_cubic_quadraticKernelBases_relabel p σ y
    (eightPointQuadraticEvaluationKernelBasis n (fun k => y (σ k)) hn)
    (eightPointQuadraticEvaluationKernelBasis m y hm)

/-- On overlapping minor charts, both relabeling and unit changes of the
homogeneous representatives preserve the cubic-plus-quadratic ideal. -/
theorem quadraticKernelMinorIdeal_scale_relabel
    {R : Type u} [CommRing R]
    (m n : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (σ : Equiv.Perm (Fin 8))
    (a : Fin 8 → R) (ha : ∀ i, IsUnit (a i))
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m y).det)
    (hn : IsUnit (eightPointQuadraticEvaluationMinor n
      (fun k j => a k * y (σ k) j)).det)
    (p : MvPolynomial (Fin 4) R) :
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients
        (eightPointQuadraticEvaluationKernelBasis n
          (fun k j => a k * y (σ k) j) hn i).1))) =
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      quadraticPolynomialOfCoefficients
        (eightPointQuadraticEvaluationKernelBasis m y hm i).1))) :=
  ideal_span_cubic_quadraticKernelBases_of_kernel_eq p
    (fun k j => a k * y (σ k) j) y
    (eightPointQuadraticEvaluationKernel_scale_relabel σ a ha y)
    (eightPointQuadraticEvaluationKernelBasis n
      (fun k j => a k * y (σ k) j) hn)
    (eightPointQuadraticEvaluationKernelBasis m y hm)

/-- A selected minor chart is stable under relabeling and unit rescaling
of projective representatives, and its resulting intersection ideal is
unchanged. -/
theorem quadraticKernelMinorIdeal_scale_relabel_sameMinor
    {R : Type u} [CommRing R]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (σ : Equiv.Perm (Fin 8))
    (a : Fin 8 → Rˣ)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m y).det)
    (p : MvPolynomial (Fin 4) R) :
    ∃ hn : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => (a k : R) * y (σ k) j)).det,
      Ideal.span (insert p (Set.range (fun i : Fin 2 =>
        quadraticPolynomialOfCoefficients
          (eightPointQuadraticEvaluationKernelBasis m
            (fun k j => (a k : R) * y (σ k) j) hn i).1))) =
      Ideal.span (insert p (Set.range (fun i : Fin 2 =>
        quadraticPolynomialOfCoefficients
          (eightPointQuadraticEvaluationKernelBasis m y hm i).1))) := by
  have hperm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k => y (σ k))).det :=
    (eightPointQuadraticEvaluationMinor_isUnit_det_perm_iff m σ y).2 hm
  have hn : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => (a k : R) * y (σ k) j)).det :=
    (eightPointQuadraticEvaluationMinor_isUnit_det_scale_iff m a
      (fun k => y (σ k))).2 hperm
  exact ⟨hn, quadraticKernelMinorIdeal_scale_relabel m m y σ
    (fun k => (a k : R)) (fun k => Units.isUnit (a k)) hm hn p⟩

/-- At a field-valued point where both chosen minors are invertible,
relabeling the eight points and changing the selected minor preserves the
ideal generated by the actual specialized quadratic equations and a fixed
cubic. -/
theorem selectedQuadraticOpenIdeal_relabel
    {R : Type u} [CommRing R]
    {F : Type v} [Field F]
    (m n : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (f : R →+* F)
    (σ : Equiv.Perm (Fin 8))
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    (hn : IsUnit (eightPointQuadraticEvaluationMinor n
      (fun k j => f (y (σ k) j))).det)
    (p : MvPolynomial (Fin 4) F) :
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      (quadraticSelectedOpenPolynomial n (fun k => y (σ k)) i).map
        (quadraticMinorSelectedPointLift n (fun k => y (σ k)) f hn)))) =
    Ideal.span (insert p (Set.range (fun i : Fin 2 =>
      (quadraticSelectedOpenPolynomial m y i).map
        (quadraticMinorSelectedPointLift m y f hm)))) := by
  let b := quadraticSelectedOpenBasisSpecializedBasis n
    (fun k => y (σ k)) f hn
  let c := quadraticSelectedOpenBasisSpecializedBasis m y f hm
  have h := ideal_span_cubic_quadraticKernelBases_relabel p σ
    (fun k j => f (y k j)) b c
  have hleft :
      (fun i : Fin 2 =>
        (quadraticSelectedOpenPolynomial n (fun k => y (σ k)) i).map
          (quadraticMinorSelectedPointLift n (fun k => y (σ k)) f hn)) =
      (fun i => quadraticPolynomialOfCoefficients (b i).1) := by
    funext i
    rw [quadraticSelectedOpenPolynomial_map_selectedPoint]
    simp only [b, quadraticSelectedOpenBasisSpecializedBasis_apply]
  have hright :
      (fun i : Fin 2 =>
        (quadraticSelectedOpenPolynomial m y i).map
          (quadraticMinorSelectedPointLift m y f hm)) =
      (fun i => quadraticPolynomialOfCoefficients (c i).1) := by
    funext i
    rw [quadraticSelectedOpenPolynomial_map_selectedPoint]
    simp only [c, quadraticSelectedOpenBasisSpecializedBasis_apply]
  rw [hleft, hright]
  exact h

end PfaffianDescent
