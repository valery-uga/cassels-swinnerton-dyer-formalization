import PfaffianDescent.WholeQuotientMonomialIdealBaseChange286

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
open scoped Matrix
universe u v w
variable {A : Type u} [CommRing A] {D : Type v} [CommRing D] {m n : ℕ}
variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)

/-- Chart membership is precisely the actual monomial basis condition on
an entire polynomial ideal, with the ideal itself as the datum. -/
def MonomialWholeIdealChart287 :=
  { I : Ideal (MvPolynomial (Fin m) A) //
    ∃ b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I),
      ∀ j, b j = Ideal.Quotient.mk I (monomial (B j) 1) }

def monomialWholeIdealChartBasis287 (x : MonomialWholeIdealChart287 (A := A) B) :
    Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ x.val) :=
  Classical.choose x.property

lemma monomialWholeIdealChartBasis_apply287
    (x : MonomialWholeIdealChart287 (A := A) B) (j : Fin n) :
    monomialWholeIdealChartBasis287 B x j =
      Ideal.Quotient.mk x.val (monomial (B j) 1) :=
  Classical.choose_spec x.property j

lemma cyclicPolynomialQuotientBasis_repr287
    (rho : MvPolynomial (Fin m) A →ₐ[A] Module.End A (Fin n → A))
    (v : Fin n → A)
    (hB : ∀ j, rho (monomial (B j) 1) v = Pi.single j 1)
    (q : MvPolynomial (Fin m) A ⧸ RingHom.ker rho.toRingHom) (a : Fin n) :
    (cyclicPolynomialQuotientMonomialBasis281 rho v B hB).repr q a =
      cyclicPolynomialQuotientLinearEquiv281 rho v B hB q a := by
  simp only [cyclicPolynomialQuotientMonomialBasis281, Basis.map_repr,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, Pi.basisFun_repr]

lemma cyclicMatrixQuotient_leftMulMatrix287
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A)) (i : Fin m) :
    Algebra.leftMulMatrix
      (cyclicPolynomialQuotientMonomialBasis281
        (commutingMatrixPolynomialAction282 M.matrices M.commute) (Pi.single k 1) B M.cyclic)
      (Ideal.Quotient.mk (RingHom.ker
        (commutingMatrixPolynomialAction282 M.matrices M.commute).toRingHom) (X i)) =
      M.matrices i := by
  classical
  ext a j
  rw [Algebra.leftMulMatrix_eq_repr_mul, cyclicPolynomialQuotientMonomialBasis_apply281,
    ← map_mul, cyclicPolynomialQuotientBasis_repr287,
    cyclicPolynomialQuotientLinearEquiv_mk281]
  rw [map_mul, Module.End.mul_apply, M.cyclic,
    commutingMatrixPolynomialAction_X282, Matrix.toLinAlgEquiv'_apply,
    Matrix.mulVec_single_one, Matrix.col_apply]

def cyclicMatrixWholeIdealChart287 (M : CyclicCommutingMatrixPoint283 m n B k (A := A)) :
    MonomialWholeIdealChart287 (A := A) B :=
  ⟨RingHom.ker (commutingMatrixPolynomialAction282 M.matrices M.commute).toRingHom,
    cyclicPolynomialQuotientMonomialBasis281
      (commutingMatrixPolynomialAction282 M.matrices M.commute) (Pi.single k 1) B M.cyclic,
    cyclicPolynomialQuotientMonomialBasis_apply281
      (commutingMatrixPolynomialAction282 M.matrices M.commute) (Pi.single k 1) B M.cyclic⟩

def monomialWholeIdealChartPoint287 (hk : B k = 0)
    (x : MonomialWholeIdealChart287 (A := A) B) :
    CyclicCommutingMatrixPoint283 m n B k (A := A) :=
  wholeQuotientCyclicMatrixPoint283 x.val (monomialWholeIdealChartBasis287 B x) B k
    (monomialWholeIdealChartBasis_apply287 B x) hk

lemma monomialWholeIdealChartPoint_chart287 (hk : B k = 0)
    (x : MonomialWholeIdealChart287 (A := A) B) :
    cyclicMatrixWholeIdealChart287 B k (monomialWholeIdealChartPoint287 B k hk x) = x := by
  apply Subtype.ext
  exact wholeQuotientPolynomialAction_ker_eq283 x.val (monomialWholeIdealChartBasis287 B x)

lemma cyclicMatrixWholeIdealChart_point287 (hk : B k = 0)
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A)) :
    monomialWholeIdealChartPoint287 B k hk (cyclicMatrixWholeIdealChart287 B k M) = M := by
  let bM := cyclicPolynomialQuotientMonomialBasis281
    (commutingMatrixPolynomialAction282 M.matrices M.commute) (Pi.single k 1) B M.cyclic
  have hb : monomialWholeIdealChartBasis287 B (cyclicMatrixWholeIdealChart287 B k M) = bM := by
    apply DFunLike.ext
    intro j
    exact (monomialWholeIdealChartBasis_apply287 B _ j).trans
      (cyclicPolynomialQuotientMonomialBasis_apply281
        (commutingMatrixPolynomialAction282 M.matrices M.commute) (Pi.single k 1) B M.cyclic j).symm
  apply CyclicCommutingMatrixPoint283.ext
  change wholeQuotientMultiplicationMatrix283
    (RingHom.ker (commutingMatrixPolynomialAction282 M.matrices M.commute).toRingHom)
    (monomialWholeIdealChartBasis287 B (cyclicMatrixWholeIdealChart287 B k M)) = M.matrices
  rw [hb]
  funext i
  exact cyclicMatrixQuotient_leftMulMatrix287 B k M i

def cyclicMatrixWholeIdealChartEquiv287 (hk : B k = 0) :
    CyclicCommutingMatrixPoint283 m n B k (A := A) ≃ MonomialWholeIdealChart287 (A := A) B where
  toFun := cyclicMatrixWholeIdealChart287 B k
  invFun := monomialWholeIdealChartPoint287 B k hk
  left_inv := cyclicMatrixWholeIdealChart_point287 B k hk
  right_inv := monomialWholeIdealChartPoint_chart287 B k hk

def cyclicMatrixPointMap287 (f : A →+* D)
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A)) :
    CyclicCommutingMatrixPoint283 m n B k (A := D) where
  matrices i := (M.matrices i).map f
  commute := commutingMatrix_tuple_map_commute285 M.matrices M.commute f
  cyclic := commutingMatrixAction_cyclic_map285 M.matrices M.commute f
    (fun i => (M.matrices i).map f)
    (commutingMatrix_tuple_map_commute285 M.matrices M.commute f) (fun _ => rfl) B k M.cyclic

def monomialWholeIdealChartMap287 (hk : B k = 0) (f : A →+* D)
    (x : MonomialWholeIdealChart287 (A := A) B) :
    MonomialWholeIdealChart287 (A := D) B :=
  ⟨x.val.map (MvPolynomial.map f),
    wholeQuotientBaseChanged_monomialBasis_exists286 x.val
      (monomialWholeIdealChartBasis287 B x) f B k (monomialWholeIdealChartBasis_apply287 B x) hk⟩

lemma cyclicMatrixWholeIdealChart_map287 (hk : B k = 0) (f : A →+* D)
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A)) :
    cyclicMatrixWholeIdealChart287 B k (cyclicMatrixPointMap287 B k f M) =
      monomialWholeIdealChartMap287 B k hk f (cyclicMatrixWholeIdealChart287 B k M) := by
  apply Subtype.ext
  exact (commutingMatrixActionKernel_mapped285 M.matrices M.commute f B k M.cyclic).symm

lemma monomialWholeIdealChartPoint_map287 (hk : B k = 0) (f : A →+* D)
    (x : MonomialWholeIdealChart287 (A := A) B) :
    monomialWholeIdealChartPoint287 B k hk (monomialWholeIdealChartMap287 B k hk f x) =
      cyclicMatrixPointMap287 B k f (monomialWholeIdealChartPoint287 B k hk x) := by
  apply (cyclicMatrixWholeIdealChartEquiv287 (A := D) B k hk).injective
  change cyclicMatrixWholeIdealChart287 B k
      (monomialWholeIdealChartPoint287 B k hk (monomialWholeIdealChartMap287 B k hk f x)) =
    cyclicMatrixWholeIdealChart287 B k
      (cyclicMatrixPointMap287 B k f (monomialWholeIdealChartPoint287 B k hk x))
  rw [monomialWholeIdealChartPoint_chart287, cyclicMatrixWholeIdealChart_map287,
    monomialWholeIdealChartPoint_chart287]

lemma monomialWholeIdealChartMap_id287 (hk : B k = 0)
    (x : MonomialWholeIdealChart287 (A := A) B) :
    monomialWholeIdealChartMap287 B k hk (RingHom.id A) x = x := by
  apply Subtype.ext
  change x.val.map (MvPolynomial.map (RingHom.id A)) = x.val
  have he : MvPolynomial.map (RingHom.id A) = RingHom.id (MvPolynomial (Fin m) A) :=
    RingHom.ext MvPolynomial.map_id
  rw [he, Ideal.map_id]

lemma monomialWholeIdealChartMap_comp287
    {E : Type w} [CommRing E] (hk : B k = 0)
    (f : A →+* D) (g : D →+* E) (x : MonomialWholeIdealChart287 (A := A) B) :
    monomialWholeIdealChartMap287 B k hk (g.comp f) x =
      monomialWholeIdealChartMap287 B k hk g (monomialWholeIdealChartMap287 B k hk f x) := by
  apply Subtype.ext
  change x.val.map (MvPolynomial.map (g.comp f)) =
    (x.val.map (MvPolynomial.map f)).map (MvPolynomial.map g)
  have he : (MvPolynomial.map (σ := Fin m) g).comp (MvPolynomial.map f) =
      MvPolynomial.map (g.comp f) :=
    RingHom.ext (MvPolynomial.map_map f g)
  rw [Ideal.map_map, he]

variable (R : Type u) [CommRing R] [Algebra R A]

def cyclicCoefficientWholeIdealChartEquiv287 (hk : B k = 0) :
    (UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) ≃
      MonomialWholeIdealChart287 (A := A) B :=
  (cyclicCoefficientPointEquiv283 R m n B k).trans
    (cyclicMatrixWholeIdealChartEquiv287 B k hk)

lemma cyclicCoefficientPoint_map287
    {E : Type u} [CommRing E] [Algebra R E]
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) (f : A →ₐ[R] E) :
    cyclicCoefficientPoint283 R m n B k (f.comp p) =
      cyclicMatrixPointMap287 B k f.toRingHom (cyclicCoefficientPoint283 R m n B k p) := by
  apply CyclicCommutingMatrixPoint283.ext
  funext i a j
  rfl

/-- Naturality of the actual coefficient-point / entire-ideal chart bijection. -/
lemma cyclicCoefficientWholeIdealChartEquiv_natural287
    {E : Type u} [CommRing E] [Algebra R E] (hk : B k = 0)
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) (f : A →ₐ[R] E) :
    cyclicCoefficientWholeIdealChartEquiv287 B k R hk (f.comp p) =
      monomialWholeIdealChartMap287 B k hk f.toRingHom
        (cyclicCoefficientWholeIdealChartEquiv287 B k R hk p) := by
  change cyclicMatrixWholeIdealChart287 B k (cyclicCoefficientPoint283 R m n B k (f.comp p)) = _
  rw [cyclicCoefficientPoint_map287]
  exact cyclicMatrixWholeIdealChart_map287 B k hk f.toRingHom
    (cyclicCoefficientPoint283 R m n B k p)

end PfaffianDescent
