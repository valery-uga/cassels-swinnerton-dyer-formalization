import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.PolynomialCoordinateOne
import Mathlib.Logic.Equiv.Fin.Basic

/-! SOURCE ONLY312. Explicit three-variable normalized polynomial chart of
the SAME original projective hypersurface, over ANY commutative coefficient
ring. Elimination of X_j=1 is derived, not omitted. This supplies physical
coordinate identification, not a formal-smoothness or classification premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Imposing an original equation commutes with eliminating X_j=1 over any
commutative ring; the existing field-only dimension provider is untouched. -/
def originalCoordinateOneEquationQuotientEquiv312
    {R : Type u} [CommRing R] {σ : Type} (j : σ) (p : MvPolynomial σ R) :
    (MvPolynomial σ R ⧸ (Ideal.span {p} ⊔ coordinateOneIdeal j)) ≃ₐ[R]
      (MvPolynomial {i : σ // i ≠ j} R ⧸ Ideal.span {coordinateOneEvaluation j p}) := by
  let I : Ideal (MvPolynomial σ R) := coordinateOneIdeal j
  let J : Ideal (MvPolynomial σ R) := Ideal.span {p}
  let E := coordinateOneQuotientEquiv (R := R) j
  have hJ : Ideal.span {coordinateOneEvaluation j p} =
      (J.map (Ideal.Quotient.mkₐ R I)).map E.toRingHom := by
    simp [J, I, Ideal.map_span, E, coordinateOneQuotientEquiv_mk]
  exact (Ideal.quotientEquivAlgOfEq R (sup_comm J I)).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R I J).symm.trans
      (Ideal.quotientEquivAlg (J.map (Ideal.Quotient.mkₐ R I))
        (Ideal.span {coordinateOneEvaluation j p}) E hJ))

/-- Specified original normalized equation on the other three coordinates. -/
def originalNormalizedHypersurfacePolynomial312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R) (j : Fin 4) :
    MvPolynomial (Fin 3) R :=
  (renameEquiv R (finSuccAboveEquiv j).symm) (coordinateOneEvaluation j p)

private lemma originalCoordinateOneEvaluation_coefficientMap312
    {R S : Type u} [CommRing R] [CommRing S] {σ : Type}
    (b : R →+* S) (j : σ) :
    (MvPolynomial.map b).comp (coordinateOneEvaluation (R := R) j).toRingHom =
      (coordinateOneEvaluation (R := S) j).toRingHom.comp (MvPolynomial.map b) := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [coordinateOneEvaluation]
  · intro i
    by_cases hi : i = j
    · subst i
      simp [coordinateOneEvaluation]
    · simp [coordinateOneEvaluation, hi]

/-- The specified normalized original equation commutes with ANY physical
coefficient change, including the square-zero reductions used by195. -/
lemma originalNormalizedHypersurfacePolynomial_map312
    {R S : Type u} [CommRing R] [CommRing S]
    (b : R →+* S) (p : MvPolynomial (Fin 4) R) (j : Fin 4) :
    (originalNormalizedHypersurfacePolynomial312 p j).map b =
      originalNormalizedHypersurfacePolynomial312 (p.map b) j := by
  change MvPolynomial.map b (rename (finSuccAboveEquiv j).symm
    (coordinateOneEvaluation (R := R) j p)) =
      rename (finSuccAboveEquiv j).symm (coordinateOneEvaluation (R := S) j (p.map b))
  rw [MvPolynomial.map_rename]
  exact congrArg (rename (finSuccAboveEquiv j).symm)
    (DFunLike.congr_fun (originalCoordinateOneEvaluation_coefficientMap312 b j) p)

abbrev OriginalNormalizedHypersurfaceAlgebra312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R) (j : Fin 4) :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span {originalNormalizedHypersurfacePolynomial312 p j}

noncomputable local instance originalNormalizedChartAlgebra312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R)
    {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4) :
    Algebra R (ChartRing (equationIdeal p hp) j) :=
  (chartBaseMap (equationIdeal p hp) j).toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Native actual projective chart algebra is the literal single-equation
polynomial hypersurface, with the ORIGINAL coefficient map preserved. -/
def originalNormalizedHypersurfaceChartAlgEquiv312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R)
    {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4) :
    ChartRing (equationIdeal p hp) j ≃ₐ[R] OriginalNormalizedHypersurfaceAlgebra312 p j := by
  let eC : (MvPolynomial (Fin 4) R ⧸
      (Ideal.span {p} ⊔ coordinateOneIdeal j)) ≃ₐ[R]
        ChartRing (equationIdeal p hp) j :=
    { chartPresentationEquiv (equationIdeal p hp) j with
      commutes' := by
        intro r
        change chartPresentationEquiv (equationIdeal p hp) j
          (Ideal.Quotient.mk _ (C r)) = chartBaseMap (equationIdeal p hp) j r
        exact (chartPresentationEquiv_mk (equationIdeal p hp) j (C r)).trans
          (eval₂_C _ _ r) }
  let E := renameEquiv R (finSuccAboveEquiv j).symm
  let eQ := Ideal.quotientEquivAlg
    (Ideal.span {coordinateOneEvaluation j p})
    (Ideal.span {originalNormalizedHypersurfacePolynomial312 p j}) E
    (by simp [originalNormalizedHypersurfacePolynomial312, E, Ideal.map_span])
  exact eC.symm.trans ((originalCoordinateOneEquationQuotientEquiv312 j p).trans eQ)

lemma originalNormalizedHypersurfaceChartAlgEquiv_base312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R)
    {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4) (r : R) :
    originalNormalizedHypersurfaceChartAlgEquiv312 p hp j
        (chartBaseMap (equationIdeal p hp) j r) =
      algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j) r :=
  (originalNormalizedHypersurfaceChartAlgEquiv312 p hp j).commutes r

/-- Actual Spec isomorphism; no affine presentation is supplied by a caller. -/
def originalNormalizedHypersurfaceChartSpecIso312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R)
    {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4) :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 p j)) ≅
      Spec (.of (ChartRing (equationIdeal p hp) j)) :=
  Scheme.Spec.mapIso
    (originalNormalizedHypersurfaceChartAlgEquiv312 p hp j).toRingEquiv.toCommRingCatIso.op

/-- The literal affine polynomial hypersurface is a native open chart in
the SAME original projective hypersurface. -/
def originalNormalizedHypersurfaceChartEmbedding312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R)
    {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4) :
    Spec (.of (OriginalNormalizedHypersurfaceAlgebra312 p j)) ⟶ hypersurface p hp :=
  (originalNormalizedHypersurfaceChartSpecIso312 p hp j).hom ≫ chartι (equationIdeal p hp) j

lemma originalNormalizedHypersurfaceChartEmbedding_isOpenImmersion312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R)
    {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4) :
    IsOpenImmersion (originalNormalizedHypersurfaceChartEmbedding312 p hp j) := by
  letI : IsOpenImmersion (chartι (equationIdeal p hp) j) :=
    isOpenImmersion_chartι (equationIdeal p hp) j
  exact IsOpenImmersion.comp
    (originalNormalizedHypersurfaceChartSpecIso312 p hp j).hom
    (chartι (equationIdeal p hp) j)

private lemma originalNormalizedSpecScalarComposition312
    {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
    (c : R →+* C) (e : C →+* A) (a : R →+* A) (h : e.comp c = a) :
    Spec.map (CommRingCat.ofHom e) ≫ Spec.map (CommRingCat.ofHom c) =
      Spec.map (CommRingCat.ofHom a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The original polynomial scalar map is the original projective base map
on this chart, rather than merely an isomorphism of unstructured schemes. -/
lemma originalNormalizedHypersurfaceChartEmbedding_toBase312
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R)
    {d : ℕ} (hp : p.IsHomogeneous d) (j : Fin 4) :
    originalNormalizedHypersurfaceChartEmbedding312 p hp j ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j))) := by
  have hscalar : (originalNormalizedHypersurfaceChartAlgEquiv312 p hp j).toRingHom.comp
      (chartBaseMap (equationIdeal p hp) j) =
        algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j) :=
    RingHom.ext (originalNormalizedHypersurfaceChartAlgEquiv_base312 p hp j)
  change ((originalNormalizedHypersurfaceChartSpecIso312 p hp j).hom ≫
    chartι (equationIdeal p hp) j) ≫ toBase (equationIdeal p hp) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (originalNormalizedHypersurfaceChartSpecIso312 p hp j).hom ≫ a)
      (chartι_toBase (equationIdeal p hp) j)).trans
        (originalNormalizedSpecScalarComposition312
          (chartBaseMap (equationIdeal p hp) j)
          (originalNormalizedHypersurfaceChartAlgEquiv312 p hp j).toRingHom
          (algebraMap R (OriginalNormalizedHypersurfaceAlgebra312 p j)) hscalar))

end PfaffianDescent
end
