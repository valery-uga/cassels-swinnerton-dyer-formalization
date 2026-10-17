import PfaffianDescent.PolynomialContainmentChart291

noncomputable section
namespace PfaffianDescent
open MvPolynomial
universe u

/-- The literal finite coefficient-equation ideal commutes with arbitrary
ring maps, before any original coefficient quotient is inserted. -/
lemma cyclicPolynomialContainmentIdeal_map310
    {A D : Type u} [CommRing A] [CommRing D] {m n : ℕ}
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (f : A →+* D) (p : MvPolynomial (Fin m) A) :
    (cyclicPolynomialContainmentIdeal291 B k M p).map f =
      cyclicPolynomialContainmentIdeal291 B k
        (cyclicMatrixPointMap287 B k f M) (MvPolynomial.map f p) := by
  unfold cyclicPolynomialContainmentIdeal291
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact (cyclicPolynomialContainmentCoefficient_map291 B k M f p a).symm

/-- Same whole ideals give the same containment equations after every scalar
specialization; the monomial bases and matrix coordinates may differ. -/
lemma cyclicPolynomialContainmentIdeal_kernel_iff_of_sameWholeIdeal310
    {A D : Type u} [CommRing A] [CommRing D] {m n : ℕ}
    (B C : Fin n → (Fin m →₀ ℕ)) (k l : Fin n) (hk : B k = 0) (hl : C l = 0)
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (N : CyclicCommutingMatrixPoint283 m n C l (A := A))
    (h : (cyclicMatrixWholeIdealChart287 B k M).val =
      (cyclicMatrixWholeIdealChart287 C l N).val)
    (f : A →+* D) (p : MvPolynomial (Fin m) A) :
    cyclicPolynomialContainmentIdeal291 B k M p ≤ RingHom.ker f ↔
      cyclicPolynomialContainmentIdeal291 C l N p ≤ RingHom.ker f := by
  rw [cyclicPolynomialContainmentIdeal_le_ker_iff291,
    cyclicPolynomialContainmentIdeal_le_ker_iff291,
    cyclicMatrixWholeIdealChart_map287 B k hk f M,
    cyclicMatrixWholeIdealChart_map287 C l hl f N]
  change MvPolynomial.map f p ∈ (cyclicMatrixWholeIdealChart287 B k M).val.map
      (MvPolynomial.map f) ↔
    MvPolynomial.map f p ∈ (cyclicMatrixWholeIdealChart287 C l N).val.map
      (MvPolynomial.map f)
  rw [h]

/-- Equality of the entire polynomial ideals forces equality of the entire
coefficient-equation ideals, not merely their reduced zero sets. -/
lemma cyclicPolynomialContainmentIdeal_eq_of_sameWholeIdeal310
    {A : Type u} [CommRing A] {m n : ℕ}
    (B C : Fin n → (Fin m →₀ ℕ)) (k l : Fin n) (hk : B k = 0) (hl : C l = 0)
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A))
    (N : CyclicCommutingMatrixPoint283 m n C l (A := A))
    (h : (cyclicMatrixWholeIdealChart287 B k M).val =
      (cyclicMatrixWholeIdealChart287 C l N).val)
    (p : MvPolynomial (Fin m) A) :
    cyclicPolynomialContainmentIdeal291 B k M p =
      cyclicPolynomialContainmentIdeal291 C l N p := by
  apply le_antisymm
  · have he := cyclicPolynomialContainmentIdeal_kernel_iff_of_sameWholeIdeal310
      B C k l hk hl M N h
      (Ideal.Quotient.mk (cyclicPolynomialContainmentIdeal291 C l N p)) p
    simp only [Ideal.mk_ker] at he
    exact he.mpr le_rfl
  · have he := cyclicPolynomialContainmentIdeal_kernel_iff_of_sameWholeIdeal310
      B C k l hk hl M N h
      (Ideal.Quotient.mk (cyclicPolynomialContainmentIdeal291 B k M p)) p
    simp only [Ideal.mk_ker] at he
    exact he.mp le_rfl

end PfaffianDescent
end
